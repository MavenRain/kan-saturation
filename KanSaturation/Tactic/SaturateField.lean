import KanSaturation.Core.Constraint
import KanSaturation.Core.Eval
import KanSaturation.Core.OrderedField
import KanSaturation.Core.Collapse
import KanSaturation.Core.Engine
import KanSaturation.Instances.OrderedField
import KanSaturation.Tactic.Reify
import KanTactics
import Lean

/-!
# `KanSaturation.Tactic.SaturateField`

The ordered-field (`linarith`) half of the tactic layer: a verified **denominator-clearing**
reifier for `ℚ` expressions, and the certificate replay that turns an
`OrderedField.solve` refutation into a kernel-checked proof of `False` over `ℚ`.

Mirrors the integer reifier/replay (`Tactic.Saturate`) with three differences, all
reflecting that `linarith` is the ordered-field decider rather than `omega`:

* **No tightening.**  A strict hypothesis `lhs < rhs` reifies to a genuine `<` fact
  (`holdsK_lt_of_diff`); the integer leg's `a < b ↦ a + 1 ≤ b` step is absent, so
  `0 < x ∧ x < 1` saturates without refutation over `ℚ`.
* **Denominator clearing.**  The reifier returns, with each form, a positive integer
  denominator `d` and a proof `(d : ℚ) * e = form.evalK env`; `d` accumulates as the
  product of the divisors met, so the engine only sees integer-coefficient constraints
  (`x / 2 ≤ 1` clears to `x ≤ 2`).
* **Strict fold.**  The replay tracks whether the running combination is `≤` or `<`
  (a strict fact scaled by a positive coefficient makes it `<`), closing with
  `falseK_of_fold` or its strict analogue `falseK_of_fold_lt`.

This is meta-programming on `Expr` (exempt from the kan-tactics-only rule), Mathlib-free,
and total/`Option`-returning, with the single boundary `throwError` living in the shared
`kan_saturate` elaborator.
-/

open Lean Lean.Meta Lean.Elab.Tactic

namespace KanSaturation

deriving instance ToExpr for Rel
deriving instance ToExpr for LinForm
deriving instance ToExpr for Fact

namespace Tactic

/-- `env : Nat → ℚ` as `fun i => atoms.toList.getD i 0`, so `env (lit i)` reduces to the
i-th interned (rational) atom. -/
def buildEnvQ (atoms : Array Expr) : MetaM Expr := do
  let listExpr ← mkListLit (mkConst ``Rat) atoms.toList
  let body := mkApp4 (mkConst ``List.getD [Level.zero]) (mkConst ``Rat) listExpr
    (mkBVar 0) (toExpr (0 : Rat))
  pure (mkLambda `i BinderInfo.default (mkConst ``Nat) body)

/-- Recognize a nonnegative rational *integer* literal `(OfNat n : ℚ)`, returning its
value and a proof `e = ((value : Int) : ℚ)` (the cast bridge `Rat.intCast_ofNat`). -/
def ratIntLit? (e : Expr) : MetaM (Option (Int × Expr)) := do
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[ty, n, _]) =>
      if ty.isConstOf ``Rat then
        if let .lit (.natVal k) := n then
          let pf ← mkEqSymm (← mkAppOptM ``Rat.intCast_ofNat #[some n])
          pure (some (Int.ofNat k, pf))
        else pure none
      else pure none
  | _ => pure none

/-- Verified denominator-clearing reification at `ℚ`: returns `(form, d, proof)` with
`d ≥ 1` and `proof : ((d : Int) : ℚ) * e = form.evalK env`, interning atoms.  Handles
`+`, `-`, unary `-`, integer-literal scaling, integer literals, and division by a nonzero
integer literal; any other shape is interned as an opaque atom (always sound). -/
partial def reifyEvalProofQ (envExpr : Expr) (e : Expr) :
    StateT (Array Expr) MetaM (LinForm × Int × Expr) := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => do
      let (fa, da, pa) ← reifyEvalProofQ envExpr a
      let (fb, db, pb) ← reifyEvalProofQ envExpr b
      let f := (fa.scale db).add (fb.scale da)
      let pf ← mkAppM ``OrderedField.reifyQ_add
        #[envExpr, toExpr fa, toExpr fb, toExpr da, toExpr db, a, b, pa, pb]
      pure (f, da * db, pf)
  | (``HSub.hSub, #[_, _, _, _, a, b]) => do
      let (fa, da, pa) ← reifyEvalProofQ envExpr a
      let (fb, db, pb) ← reifyEvalProofQ envExpr b
      let f := (fa.scale db).add (fb.scale (-da))
      let pf ← mkAppM ``OrderedField.reifyQ_sub
        #[envExpr, toExpr fa, toExpr fb, toExpr da, toExpr db, a, b, pa, pb]
      pure (f, da * db, pf)
  | (``Neg.neg, #[_, _, a]) => do
      let (fa, da, pa) ← reifyEvalProofQ envExpr a
      let pf ← mkAppM ``OrderedField.reifyQ_neg #[envExpr, toExpr fa, toExpr da, a, pa]
      pure (fa.scale (-1), da, pf)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => do
      match ← ratIntLit? a with
      | some (k, _) => do
          let (fb, db, pb) ← reifyEvalProofQ envExpr b
          let pf ← mkAppM ``OrderedField.reifyQ_mul_const
            #[envExpr, toExpr fb, toExpr db, b, toExpr k, pb]
          let cong ← mkCongrArg (← mkLamMulConst envExpr db b) (← litEqOf a k)
          pure (fb.scale k, db, ← mkEqTrans cong pf)
      | none => do
          match ← ratIntLit? b with
          | some (k, _) => do
              let (fa, da, pa) ← reifyEvalProofQ envExpr a
              let kCast ← mkIntCastRat k
              let pf ← mkAppM ``OrderedField.reifyQ_mul_const
                #[envExpr, toExpr fa, toExpr da, a, toExpr k, pa]
              -- (da)*(a * k) = (da)*(↑k * a): coerce the right-hand literal, then commute,
              -- so the goal matches `reifyQ_mul_const`'s left-literal LHS.
              let inner ← mkEqTrans (← mkCongrArg (← mkLamMulOperand a) (← litEqOf b k))
                (← mkAppM ``OrderedField.mul_comm #[a, kCast])
              let cong ← mkCongrArg (← mkLamScaleDenom envExpr da) inner
              pure (fa.scale k, da, ← mkEqTrans cong pf)
          | none => reifyAtomQ envExpr e
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) => do
      match ← ratIntLit? b with
      | some (k, _) =>
          if k == 0 then reifyAtomQ envExpr e
          else do
            let (fa, da, pa) ← reifyEvalProofQ envExpr a
            let kCast ← mkIntCastRat k
            let hk ← mkDecideProof (← mkAppM ``Ne #[kCast, toExpr (0 : Rat)])
            let pf ← mkAppM ``OrderedField.reifyQ_div
              #[envExpr, toExpr fa, toExpr da, a, toExpr k, hk, pa]
            -- rewrite the divisor literal `b` to `((k:Int):ℚ)` inside the goal
            let cong ← mkCongrArg (← mkLamDivDenom envExpr (da * k) a) (← litEqOf b k)
            pure (fa, da * k, ← mkEqTrans cong pf)
      | none => reifyAtomQ envExpr e
  | (``OfNat.ofNat, _) => do
      match ← ratIntLit? e with
      | some (c, litEq) => do
          let pf ← mkAppM ``OrderedField.reifyQ_const #[envExpr, toExpr c]
          let cong ← mkCongrArg (← mkLamOneMul envExpr) litEq
          pure (LinForm.mk [] c, 1, ← mkEqTrans cong pf)
      | none => reifyAtomQ envExpr e
  | _ => reifyAtomQ envExpr e
where
  /-- Intern `e` as an atom: `((1:Int):ℚ) * e = (unit form).evalK env` (`env v` reduces to `e`). -/
  reifyAtomQ (envExpr : Expr) (e : Expr) : StateT (Array Expr) MetaM (LinForm × Int × Expr) := do
    let v ← internAtom e
    let pf ← mkAppM ``OrderedField.reifyQ_atom #[envExpr, toExpr v]
    pure (LinForm.mk [(1, v)] 0, 1, pf)
  /-- `((value : Int) : ℚ)` as an `Expr`. -/
  mkIntCastRat (value : Int) : MetaM Expr := do
    mkAppOptM ``IntCast.intCast #[some (mkConst ``Rat), none, some (toExpr value)]
  /-- The literal-cast bridge `e = ((k:Int):ℚ)` for a recognized literal `e`. -/
  litEqOf (e : Expr) (_k : Int) : MetaM Expr := do
    match ← ratIntLit? e with
    | some (_, pf) => pure pf
    | none => mkEqRefl e
  /-- `fun z => ((1:Int):ℚ) * z` (for the constant cast congruence). -/
  mkLamOneMul (_envExpr : Expr) : MetaM Expr := do
    withLocalDeclD `z (mkConst ``Rat) fun z => do
      mkLambdaFVars #[z] (← mkAppM ``HMul.hMul #[← mkIntCastRat 1, z])
  /-- `fun z => ((db:Int):ℚ) * (z * b)` (for the `k * b` cast congruence). -/
  mkLamMulConst (_envExpr : Expr) (db : Int) (b : Expr) : MetaM Expr := do
    withLocalDeclD `z (mkConst ``Rat) fun z => do
      mkLambdaFVars #[z] (← mkAppM ``HMul.hMul #[← mkIntCastRat db, ← mkAppM ``HMul.hMul #[z, b]])
  /-- `fun z => a * z` (to rewrite a right-hand literal before commuting it left). -/
  mkLamMulOperand (a : Expr) : MetaM Expr := do
    withLocalDeclD `z (mkConst ``Rat) fun z => do
      mkLambdaFVars #[z] (← mkAppM ``HMul.hMul #[a, z])
  /-- `fun z => ((d:Int):ℚ) * z` (to push a commutation under the denominator scaling). -/
  mkLamScaleDenom (_envExpr : Expr) (d : Int) : MetaM Expr := do
    withLocalDeclD `z (mkConst ``Rat) fun z => do
      mkLambdaFVars #[z] (← mkAppM ``HMul.hMul #[← mkIntCastRat d, z])
  /-- `fun z => ((d:Int):ℚ) * (a / z)` (for the divisor cast congruence). -/
  mkLamDivDenom (_envExpr : Expr) (d : Int) (a : Expr) : MetaM Expr := do
    withLocalDeclD `z (mkConst ``Rat) fun z => do
      mkLambdaFVars #[z] (← mkAppM ``HMul.hMul #[← mkIntCastRat d, ← mkAppM ``HDiv.hDiv #[a, z]])

/-- Collect local `ℚ` comparison hypotheses as `(rel, lhs, rhs, proof)` with
`rel ∈ {le, lt, eq}`; `≥`/`>` are recorded swapped (definitional). -/
def collectComparisonHypsQ : MetaM (Array (Rel × Expr × Expr × Expr)) := do
  (← getLCtx).foldlM (init := (#[] : Array (Rel × Expr × Expr × Expr))) fun acc decl => do
    if decl.isImplementationDetail then return acc
    let pf := decl.toExpr
    match decl.type.getAppFnArgs with
    | (``LE.le, #[ty, _, a, b]) =>
        if ty.isConstOf ``Rat then return acc.push (.le, a, b, pf) else return acc
    | (``LT.lt, #[ty, _, a, b]) =>
        if ty.isConstOf ``Rat then return acc.push (.lt, a, b, pf) else return acc
    | (``GE.ge, #[ty, _, a, b]) =>
        if ty.isConstOf ``Rat then return acc.push (.le, b, a, pf) else return acc
    | (``GT.gt, #[ty, _, a, b]) =>
        if ty.isConstOf ``Rat then return acc.push (.lt, b, a, pf) else return acc
    | (``Eq, #[ty, a, b]) =>
        if ty.isConstOf ``Rat then return acc.push (.eq, a, b, pf) else return acc
    | _ => return acc

/-- `lhs ≤ rhs` from `lhs = rhs` over `ℚ` (used to split an equality hypothesis into its
two `≤` directions). -/
def leOfEqRat (rhs hyp : Expr) : MetaM Expr := do
  let lam ← withLocalDeclD `z (mkConst ``Rat) fun z => do
    mkLambdaFVars #[z] (← mkAppM ``LE.le #[z, rhs])
  mkAppM ``Eq.mp #[← mkCongrArg lam (← mkEqSymm hyp), ← mkAppOptM ``Rat.le_refl #[some rhs]]

/-- Reify one comparison hypothesis into the `≤`/`<`-facts (over `ℚ`) it contributes,
each paired with its `holdsK` proof.  `=` contributes both `≤` directions; `<` stays
strict (no tightening). -/
def factsOfHyp (envExpr : Expr) (rel : Rel) (lhs rhs pf : Expr) :
    StateT (Array Expr) MetaM (Array (Fact × Expr)) := do
  let mk (loE hiE hypLe : Expr) (strict : Bool) : StateT (Array Expr) MetaM (Fact × Expr) := do
    let diff ← mkAppM ``HSub.hSub #[hiE, loE]
    let (form, d, p) ← reifyEvalProofQ envExpr diff
    let hd ← mkDecideProof (← mkAppM ``LT.lt #[toExpr (0 : Int), toExpr d])
    if strict then
      let holds ← mkAppM ``OrderedField.holdsK_lt_of_diff
        #[envExpr, toExpr form, toExpr d, loE, hiE, p, hd, hypLe]
      pure ({ rel := .lt, form }, holds)
    else
      let holds ← mkAppM ``OrderedField.holdsK_le_of_diff
        #[envExpr, toExpr form, toExpr d, loE, hiE, p, hd, hypLe]
      pure ({ rel := .le, form }, holds)
  match rel with
  | .le => pure #[← mk lhs rhs pf false]
  | .lt => pure #[← mk lhs rhs pf true]
  | .eq =>
      let le1 ← mk lhs rhs (← leOfEqRat rhs pf) false
      let le2 ← mk rhs lhs (← leOfEqRat lhs (← mkEqSymm pf)) false
      pure #[le1, le2]

/-- Intern the atoms of `e` (mirroring `reifyEvalProofQ`'s recursion exactly, so indices
agree) without building any proof — the env-independent first pass. -/
partial def discoverAtomsQ (e : Expr) : StateT (Array Expr) MetaM Unit := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => discoverAtomsQ a; discoverAtomsQ b
  | (``HSub.hSub, #[_, _, _, _, a, b]) => discoverAtomsQ a; discoverAtomsQ b
  | (``Neg.neg, #[_, _, a]) => discoverAtomsQ a
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
      match ← ratIntLit? a with
      | some _ => discoverAtomsQ b
      | none =>
          match ← ratIntLit? b with
          | some _ => discoverAtomsQ a
          | none => discard (internAtom e)
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) =>
      match ← ratIntLit? b with
      | some (k, _) => if k == 0 then discard (internAtom e) else discoverAtomsQ a
      | none => discard (internAtom e)
  | (``OfNat.ofNat, _) =>
      match ← ratIntLit? e with
      | some _ => pure ()
      | none => discard (internAtom e)
  | _ => discard (internAtom e)

/-- Run the ordered-field engine on the current `ℚ` comparison hypotheses and replay its
Farkas certificate into a kernel-checked proof of `False`.  Returns `none` when there is
no refutation, a combination references a stale index, or any coefficient is negative
(all handled as data, never thrown). -/
def proveFalseQ : MetaM (Option Expr) := do
  let hyps ← collectComparisonHypsQ
  -- pass 1: discover atoms (each hypothesis reifies `rhs - lhs`, i.e. `rhs` then `lhs`)
  let atoms ← hyps.foldlM (init := (#[] : Array Expr)) fun atoms hyp => do
    let (_, l, r, _) := hyp
    let (_, atoms) ← (do discoverAtomsQ r; discoverAtomsQ l).run atoms
    pure atoms
  let envExpr ← buildEnvQ atoms
  -- pass 2: build the facts and their `holdsK` proofs against the real environment
  let result ← hyps.foldlM (init := ((#[], atoms) : Array (Fact × Expr) × Array Expr))
    fun acc hyp => do
      let (fhs, atoms') := acc
      let (rel, l, r, pf) := hyp
      let (entries, atoms'') ← (factsOfHyp envExpr rel l r pf).run atoms'
      pure (fhs ++ entries, atoms'')
  let factsHolds := result.1
  let facts := (factsHolds.map (·.1)).toList
  -- resolve the certificate into nonzero, nonnegative-coefficient `(coeff, fact, holds)`
  let resolved : Option (List (Int × Fact × Expr)) :=
    ((OrderedField.solve facts).toOption.bind fun cert =>
      cert.combo.mapM fun ci => (factsHolds[ci.2]?).map fun fh => (ci.1, fh.1, fh.2)).bind
      fun combo =>
        let nz := combo.filter fun e => e.1 != 0
        if nz.all fun e => decide (0 < e.1) then some nz else none
  let nested ← resolved.mapM fun combo => do
    -- fold `∑ cᵢ · factᵢ`, tracking whether the running combination is `≤` (`false`) or
    -- `<` (`true`); a strict fact scaled by a positive coefficient makes it strict.
    let zeroForm : LinForm := { terms := [], const := 0 }
    let zeroProof ← mkAppM ``OrderedField.evalK_nil_nonneg #[envExpr]
    let (foldedForm, foldedProof, foldedStrict) ← combo.foldlM
      (fun (acc : LinForm × Expr × Bool) (entry : Int × Fact × Expr) => do
        let (accForm, accProof, accStrict) := acc
        let (c, fact, holds) := entry
        let scaled := fact.form.scale c
        let entryStrict := fact.rel == Rel.lt
        let scaledProof ←
          if entryStrict then
            let cPos ← mkDecideProof (← mkAppM ``LT.lt #[toExpr (0 : Int), toExpr c])
            mkAppM ``OrderedField.holdsK_lt_scale_pos #[envExpr, toExpr c, toExpr fact.form, cPos, holds]
          else
            let cNonneg ← mkDecideProof (← mkAppM ``LE.le #[toExpr (0 : Int), toExpr c])
            mkAppM ``OrderedField.holdsK_le_scale #[envExpr, toExpr c, toExpr fact.form, cNonneg, holds]
        let lemmaName : Name := match accStrict, entryStrict with
          | false, false => ``OrderedField.holdsK_le_add
          | false, true  => ``OrderedField.holdsK_lt_add_of_le_of_lt
          | true,  false => ``OrderedField.holdsK_lt_add_of_lt_of_le
          | true,  true  => ``OrderedField.holdsK_lt_add
        let addProof ← mkAppM lemmaName
          #[envExpr, toExpr accForm, toExpr scaled, accProof, scaledProof]
        pure (accForm.add scaled, addProof, accStrict || entryStrict))
      (zeroForm, zeroProof, false)
    -- the folded residual must collapse to all-zero terms with a contradictory constant
    if (collapse foldedForm.terms).all isZeroCoeff then
      if foldedStrict then
        if decide (foldedForm.const ≤ 0) then
          let hCollapse ← mkDecideProof (← mkEq
            (← mkAppM ``List.all #[← mkAppM ``collapse #[toExpr foldedForm.terms], mkConst ``isZeroCoeff])
            (toExpr true))
          let hnonpos ← mkDecideProof (← mkAppM ``LE.le #[toExpr foldedForm.const, toExpr (0 : Int)])
          pure (some (← mkAppM ``OrderedField.falseK_of_fold_lt
            #[envExpr, toExpr foldedForm, foldedProof, hCollapse, hnonpos]))
        else pure none
      else
        if decide (foldedForm.const < 0) then
          let hCollapse ← mkDecideProof (← mkEq
            (← mkAppM ``List.all #[← mkAppM ``collapse #[toExpr foldedForm.terms], mkConst ``isZeroCoeff])
            (toExpr true))
          let hneg ← mkDecideProof (← mkAppM ``LT.lt #[toExpr foldedForm.const, toExpr (0 : Int)])
          pure (some (← mkAppM ``OrderedField.falseK_of_fold
            #[envExpr, toExpr foldedForm, foldedProof, hCollapse, hneg]))
        else pure none
    else pure none
  pure nested.join

/-- Prove a single `ℚ` comparison goal by contradiction: introduce the negated comparison,
refute with `proveFalseQ`, then re-wrap with the `Rat.not_*` equivalence whose right side
is the goal. -/
def closeByNegQ (iffLemma : Name) (sideArgs : Array Expr) (negHyp : Expr) : MetaM (Option Expr) := do
  let lamOpt ← withLocalDeclD `h negHyp fun h => do
    (← proveFalseQ).mapM fun fp => mkLambdaFVars #[h] fp
  lamOpt.mapM fun lam => do mkAppM ``Iff.mp #[← mkAppOptM iffLemma (sideArgs.map some), lam]

/-- Dispatch a `ℚ` goal (`False`, `≤`, `<`, `≥`, `>`, `=`, or `¬`-comparison) to the
ordered-field replay; `none` for an unsupported goal or a failed refutation. -/
def dispatchGoalQ (goalType : Expr) : MetaM (Option Expr) := do
  let isRat (ty : Expr) : Bool := ty.isConstOf ``Rat
  match goalType.getAppFnArgs with
  | (``LE.le, #[ty, _, a, b]) =>
      if isRat ty then closeByNegQ ``Rat.not_lt #[b, a] (← mkAppM ``LT.lt #[b, a]) else pure none
  | (``LT.lt, #[ty, _, a, b]) =>
      if isRat ty then closeByNegQ ``Rat.not_le #[b, a] (← mkAppM ``LE.le #[b, a]) else pure none
  | (``GE.ge, #[ty, _, a, b]) =>
      if isRat ty then closeByNegQ ``Rat.not_lt #[a, b] (← mkAppM ``LT.lt #[a, b]) else pure none
  | (``GT.gt, #[ty, _, a, b]) =>
      if isRat ty then closeByNegQ ``Rat.not_le #[a, b] (← mkAppM ``LE.le #[a, b]) else pure none
  | (``Eq, #[ty, a, b]) =>
      if isRat ty then do
        let p1Opt ← closeByNegQ ``Rat.not_lt #[b, a] (← mkAppM ``LT.lt #[b, a])
        let p2Opt ← closeByNegQ ``Rat.not_lt #[a, b] (← mkAppM ``LT.lt #[a, b])
        (p1Opt.bind fun p1 => p2Opt.map fun p2 => (p1, p2)).mapM fun (p1, p2) =>
          mkAppM ``Rat.le_antisymm #[p1, p2]
      else pure none
  | _ => pure none

end Tactic
end KanSaturation
