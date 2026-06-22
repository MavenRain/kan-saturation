import KanSaturation.Core.Constraint
import KanSaturation.Core.Eval
import KanSaturation.Core.Reflect
import KanSaturation.Core.Collapse
import KanSaturation.Core.Tighten
import KanSaturation.Core.Engine
import KanSaturation.Instances.Integer
import KanSaturation.Tactic.Reify
import KanSaturation.Tactic.SaturateField
import KanSaturation.Tactic.SaturateIdeal
import KanTactics
import Lean

/-!
# `KanSaturation.Tactic.Saturate` (replay, part 1: verified reifier)

Meta-code turning the engine's certificate into a kernel-checked proof.  This part is
the **verified reifier**: given an integer `Expr` it returns the `LinForm` and a proof
`e = (that form).eval env`, where `env` is a concrete atom lookup so `env i` reduces to
the i-th interned atom.  Proofs are assembled from the `Core.Eval` lemmas
(`eval_add`, `eval_const`, `eval_atom`) via congruence.  Tactic-implementation
meta-code, exempt from the kan-tactics-only rule.

Scope (this part): `+`, `-`, unary `-`, multiplication by a constant factor, integer
literals, and atoms, with any other shape (including a genuinely nonlinear product)
interned as an opaque atom, which is always sound.
-/

open Lean Lean.Meta Lean.Elab.Tactic

namespace KanSaturation

-- `ToExpr` for `Rel`/`LinForm`/`Fact` is derived once in `Tactic.SaturateField` (imported).

namespace Tactic

/-- `env : Nat → Int` as `fun i => atoms.toList.getD i 0`, so `env (lit i)` reduces to
the i-th interned atom. -/
def buildEnv (atoms : Array Expr) : MetaM Expr := do
  let listExpr ← mkListLit (mkConst ``Int) atoms.toList
  let body := mkApp4 (mkConst ``List.getD [Level.zero]) (mkConst ``Int) listExpr
    (mkBVar 0) (toExpr (0 : Int))
  pure (mkLambda `i BinderInfo.default (mkConst ``Nat) body)

/-- Intern `e` as an atom and return its unit form with the proof `e = form.eval env`
(valid because `env v` reduces to `e`). -/
def reifyAtom (envExpr : Expr) (e : Expr) : StateT (Array Expr) MetaM (LinForm × Expr) := do
  let v ← internAtom e
  let f : LinForm := { terms := [(1, v)], const := 0 }
  let lem := mkApp2 (mkConst ``LinForm.eval_atom) envExpr (toExpr v)
  pure (f, ← mkEqSymm lem)

/-- Recognize an integer-literal `Expr` (`OfNat` or `Neg` of one) and return its value. -/
partial def intLitOf? (e : Expr) : Option Int :=
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[_, n, _]) =>
      if let .lit (.natVal k) := n then some (Int.ofNat k) else none
  | (``Neg.neg, #[_, _, a]) => (intLitOf? a).map (fun k => -k)
  | _ => none

/-- Verified reification: returns `(f, proof : e = f.eval env)`, interning atoms.
Handles `+`, `-`, unary `-`, multiplication by a constant factor, integer literals, and
atoms; any other shape (including a genuinely nonlinear product) is interned as an
opaque atom, which is always sound. -/
partial def reifyEvalProof (envExpr : Expr) (e : Expr) :
    StateT (Array Expr) MetaM (LinForm × Expr) := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => do
      let (fa, pa) ← reifyEvalProof envExpr a
      let (fb, pb) ← reifyEvalProof envExpr b
      let f := fa.add fb
      let addFn := e.appFn!.appFn!
      let congr ← mkCongr (← mkCongrArg addFn pa) pb
      let lem := mkApp3 (mkConst ``LinForm.eval_add) envExpr (toExpr fa) (toExpr fb)
      pure (f, ← mkEqTrans congr (← mkEqSymm lem))
  | (``HSub.hSub, #[_, _, _, _, a, b]) => do
      let (fa, pa) ← reifyEvalProof envExpr a
      let (fb, pb) ← reifyEvalProof envExpr b
      let f := fa.add (fb.scale (-1))
      let lem := mkAppN (mkConst ``reify_sub) #[envExpr, toExpr fa, toExpr fb, a, b, pa, pb]
      pure (f, lem)
  | (``Neg.neg, #[_, _, a]) => do
      let (fa, pa) ← reifyEvalProof envExpr a
      let f := fa.scale (-1)
      let lem := mkAppN (mkConst ``reify_neg) #[envExpr, toExpr fa, a, pa]
      pure (f, lem)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => do
      -- linear only when one factor is a constant literal; prefer the left factor.
      let scaleBy : Expr → Int → Name → StateT (Array Expr) MetaM (LinForm × Expr) :=
        fun operand k lem => do
          let (f, p) ← reifyEvalProof envExpr operand
          pure (f.scale k, mkAppN (mkConst lem) #[envExpr, toExpr f, operand, toExpr k, p])
      (intLitOf? a).elim
        ((intLitOf? b).elim (reifyAtom envExpr e)
          (fun k => scaleBy a k ``reify_mul_const_r))
        (fun k => scaleBy b k ``reify_mul_const)
  | (``OfNat.ofNat, #[_, n, _]) =>
      if let .lit (.natVal k) := n then
        let c : Int := Int.ofNat k
        let f : LinForm := { terms := [], const := c }
        let lem := mkApp2 (mkConst ``LinForm.eval_const) envExpr (toExpr c)
        pure (f, ← mkEqSymm lem)
      else
        reifyAtom envExpr e
  | _ => reifyAtom envExpr e

/-- Collect the local integer comparison hypotheses, normalized to `(rel, lhs, rhs,
proofExpr)` with `rel ∈ {le, lt, eq}`.  `a ≥ b` is recorded as `b ≤ a` and `a > b` as
`b < a` (these hold definitionally, so the stored proof is reused as-is). -/
def collectComparisonHyps : MetaM (Array (Rel × Expr × Expr × Expr)) := do
  (← getLCtx).foldlM (init := (#[] : Array (Rel × Expr × Expr × Expr))) fun acc decl => do
    if decl.isImplementationDetail then return acc
    let pf := decl.toExpr
    match decl.type.getAppFnArgs with
    | (``LE.le, #[ty, _, a, b]) =>
        if ty.isConstOf ``Int then return acc.push (.le, a, b, pf) else return acc
    | (``LT.lt, #[ty, _, a, b]) =>
        if ty.isConstOf ``Int then return acc.push (.lt, a, b, pf) else return acc
    | (``GE.ge, #[ty, _, a, b]) =>
        if ty.isConstOf ``Int then return acc.push (.le, b, a, pf) else return acc
    | (``GT.gt, #[ty, _, a, b]) =>
        if ty.isConstOf ``Int then return acc.push (.lt, b, a, pf) else return acc
    | (``Eq, #[ty, a, b]) =>
        if ty.isConstOf ``Int then return acc.push (.eq, a, b, pf) else return acc
    | _ => return acc

/-- Run the engine on the current local context's integer comparisons and replay its
certificate into a kernel-checked proof of `False`.  Returns `none` when there is no
refutation (errors are values, not thrown).  Every comparison is reduced to `≤`-facts
(`0 ≤ form`): `<` is tightened by one (integer strictness `a < b ↔ a + 1 ≤ b`); `=`
contributes both directions. -/
def proveFalse : MetaM (Option Expr) := do
  let hyps ← collectComparisonHyps
  -- pass 1: discover atoms (forms do not depend on env)
  let dummy ← buildEnv #[]
  let atoms ← hyps.foldlM (init := (#[] : Array Expr)) fun atoms hyp => do
    let (_, l, r, _) := hyp
    let (_, atoms) ← (reifyEvalProof dummy l).run atoms
    let (_, atoms) ← (reifyEvalProof dummy r).run atoms
    pure atoms
  let envExpr ← buildEnv atoms
  -- pass 2: build the `≤`-facts and their `holds` proofs against the real env
  let init : Array (Fact × Expr) × Array Expr := (#[], atoms)
  let result ← hyps.foldlM (init := init) fun acc hyp => do
    let (fhs, atoms') := acc
    let (rel, l, r, pf) := hyp
    let ((formL, pL), atoms'') ← (reifyEvalProof envExpr l).run atoms'
    let ((formR, pR), atoms''') ← (reifyEvalProof envExpr r).run atoms''
    let diff := formR.add (formL.scale (-1))
    let entries ← match rel with
      | .le =>
          let fact : Fact := { rel := .le, form := diff }
          let holds := mkAppN (mkConst ``holds_le_of)
            #[envExpr, toExpr formL, toExpr formR, l, r, pL, pR, pf]
          pure #[(fact, holds)]
      | .lt =>
          let fact : Fact := { rel := .le, form := diff.add (LinForm.mk [] (-1)) }
          let holds := mkAppN (mkConst ``holds_lt_of)
            #[envExpr, toExpr formL, toExpr formR, l, r, pL, pR, pf]
          pure #[(fact, holds)]
      | .eq =>
          let factLe : Fact := { rel := .le, form := diff }
          let factGe : Fact := { rel := .le, form := formL.add (formR.scale (-1)) }
          let holdsLe := mkAppN (mkConst ``holds_le_of)
            #[envExpr, toExpr formL, toExpr formR, l, r, pL, pR, ← mkAppM ``Int.le_of_eq #[pf]]
          let holdsGe := mkAppN (mkConst ``holds_le_of)
            #[envExpr, toExpr formR, toExpr formL, r, l, pR, pL,
              ← mkAppM ``Int.le_of_eq #[← mkEqSymm pf]]
          pure #[(factLe, holdsLe), (factGe, holdsGe)]
    pure (fhs ++ entries, atoms''')
  -- integer tightening: for each `≤`-fact whose variable coefficients share a gcd `g > 1`,
  -- add the gcd-tightened fact `0 ≤ ∑(aᵢ/g)xᵢ + ⌊c/g⌋` as an *extra sound* hypothesis (its
  -- `holds` is `holds_gcdTighten` applied to the original `holds`).  This closes ℤ/ℚ gaps
  -- like `2x = 1`; the engine and Farkas replay below consume it like any other `≤`-fact.
  let tightened ← result.1.foldlM (init := (#[] : Array (Fact × Expr))) fun acc fh => do
    let (fact, holds) := fh
    let gNat := fact.form.terms.foldl (fun a ce => Nat.gcd a ce.1.natAbs) 0
    if gNat > 1 then
      let g : Int := Int.ofNat gNat
      let fact' : Fact := { rel := .le, form := fact.form.gcdTighten g }
      let hg ← mkDecideProof (← mkAppM ``LT.lt #[toExpr (0 : Int), toExpr g])
      let dvdPred ← mkAppM ``KanSaturation.dvdCoeff #[toExpr g]
      let allExpr ← mkAppM ``List.all #[toExpr fact.form.terms, dvdPred]
      let hdvd ← mkDecideProof (← mkEq allExpr (toExpr true))
      let holds' := mkAppN (mkConst ``KanSaturation.holds_gcdTighten)
        #[envExpr, toExpr g, toExpr fact.form, hg, hdvd, holds]
      pure (acc.push (fact', holds'))
    else pure acc
  let factsHolds := result.1 ++ tightened
  let facts := (factsHolds.map (·.1)).toList
  -- resolve the certificate into `(coeff, fact, holds)` triples; `none` if the engine
  -- found no refutation, a combination references a stale index, or any coefficient is
  -- negative (our replay only scales by nonnegative coefficients).  All handled as data:
  -- this guard is what keeps the `mkDecideProof (0 ≤ c)` below from ever being asked to
  -- decide a false proposition (which would throw instead of failing gracefully).
  let resolved : Option (List (Int × Fact × Expr)) :=
    ((Integer.solve facts).toOption.bind fun cert =>
      cert.combo.mapM fun ci => (factsHolds[ci.2]?).map fun fh => (ci.1, fh.1, fh.2)).bind
      fun combo => if combo.all fun e => decide (0 ≤ e.1) then some combo else none
  let nested ← resolved.mapM fun combo => do
    -- fold the certificate combination: ∑ cᵢ · factᵢ, accumulating the proof
    let zeroForm : LinForm := { terms := [], const := 0 }
    let zeroProof := mkApp (mkConst ``Int.le_refl) (toExpr (0 : Int))
    let (foldedForm, foldedProof) ← combo.foldlM
      (fun (acc : LinForm × Expr) (entry : Int × Fact × Expr) => do
        let (accForm, accProof) := acc
        let (c, fact, holds) := entry
        let scaled := fact.form.scale c
        let cNonneg ← mkDecideProof (← mkAppM ``LE.le #[toExpr (0 : Int), toExpr c])
        let scaledProof := mkAppN (mkConst ``holds_le_scale)
          #[envExpr, toExpr c, toExpr fact.form, cNonneg, holds]
        let addProof := mkAppN (mkConst ``holds_le_add)
          #[envExpr, toExpr accForm, toExpr scaled, accProof, scaledProof]
        pure (accForm.add scaled, addProof))
      (zeroForm, zeroProof)
    -- the folded residual must collapse to all-zero terms with a negative constant;
    -- otherwise the certificate does not witness a contradiction, so fail gracefully
    -- (rather than ask `mkDecideProof` to prove a false `hCollapse`/`hneg`).
    if (collapse foldedForm.terms).all isZeroCoeff && decide (foldedForm.const < 0) then
      let collapseExpr ← mkAppM ``collapse #[toExpr foldedForm.terms]
      let allExpr ← mkAppM ``List.all #[collapseExpr, mkConst ``isZeroCoeff]
      let hCollapse ← mkDecideProof (← mkEq allExpr (toExpr true))
      let hneg ← mkDecideProof (← mkAppM ``LT.lt #[toExpr foldedForm.const, toExpr (0 : Int)])
      pure (some (mkAppN (mkConst ``false_of_fold)
        #[envExpr, toExpr foldedForm, foldedProof, hCollapse, hneg]))
    else pure none
  pure nested.join

/-- Prove a single comparison goal by contradiction: introduce the negated comparison
`negHyp` as a hypothesis, refute with `proveFalse`, then re-wrap with the `Int.not_*`
equivalence `iffLemma` (applied to `sideArgs`) whose right side is the goal.  `none`
propagates when the refutation fails. -/
def closeByNeg (iffLemma : Name) (sideArgs : Array Expr) (negHyp : Expr) :
    MetaM (Option Expr) := do
  let lamOpt ← withLocalDeclD `h negHyp fun h => do
    (← proveFalse).mapM fun fp => mkLambdaFVars #[h] fp
  lamOpt.mapM fun lam => do mkAppM ``Iff.mp #[← mkAppOptM iffLemma (sideArgs.map some), lam]

/-- Refute the current context: try the integer engine, then the ordered-field one, then
the ideal one (contradictory `ℚ` equalities, via a Nullstellensatz certificate). -/
def proveFalseAny : MetaM (Option Expr) := do
  let r ← proveFalse
  if r.isSome then pure r else do
    let q ← proveFalseQ
    if q.isSome then pure q else proveFalseP

/-- Build the proof for whatever goal shape `kan_saturate` supports: `False`, an integer
or rational comparison (`≤`, `<`, `≥`, `>`, `=`), or the negation of a comparison.  The
integer comparison cases use the `omega` leg; rational ones the `linarith` leg.  Returns
`none` for an unsupported goal or a failed refutation. -/
def dispatchGoal (goalType : Expr) : MetaM (Option Expr) := do
  if goalType.isConstOf ``False then
    -- the contradictory hypotheses may be integer (`omega` leg) or rational (`linarith`
    -- leg); try the integer engine first, then the ordered-field one.
    proveFalseAny
  else do
    let isInt (ty : Expr) : Bool := ty.isConstOf ``Int
    match goalType.getAppFnArgs with
    | (``LE.le, #[ty, _, a, b]) => do
        -- a ≤ b  ⟸  ¬(b < a)
        if isInt ty then closeByNeg ``Int.not_lt #[b, a] (← mkAppM ``LT.lt #[b, a])
        else dispatchGoalQ goalType
    | (``LT.lt, #[ty, _, a, b]) => do
        -- a < b  ⟸  ¬(b ≤ a)
        if isInt ty then closeByNeg ``Int.not_le #[b, a] (← mkAppM ``LE.le #[b, a])
        else dispatchGoalQ goalType
    | (``GE.ge, #[ty, _, a, b]) => do
        -- a ≥ b  is  b ≤ a  ⟸  ¬(a < b)
        if isInt ty then closeByNeg ``Int.not_lt #[a, b] (← mkAppM ``LT.lt #[a, b])
        else dispatchGoalQ goalType
    | (``GT.gt, #[ty, _, a, b]) => do
        -- a > b  is  b < a  ⟸  ¬(a ≤ b)
        if isInt ty then closeByNeg ``Int.not_le #[a, b] (← mkAppM ``LE.le #[a, b])
        else dispatchGoalQ goalType
    | (``Eq, #[ty, a, b]) => do
        -- a = b  by antisymmetry of the two ≤ directions
        if isInt ty then
          let p1Opt ← closeByNeg ``Int.not_lt #[b, a] (← mkAppM ``LT.lt #[b, a])
          let p2Opt ← closeByNeg ``Int.not_lt #[a, b] (← mkAppM ``LT.lt #[a, b])
          (p1Opt.bind fun p1 => p2Opt.map fun p2 => (p1, p2)).mapM fun (p1, p2) =>
            mkAppM ``Int.le_antisymm #[p1, p2]
        else do
          -- a ℚ equality: the ordered-field (linarith) leg first, then the ideal one.
          let q ← dispatchGoalQ goalType
          if q.isSome then pure q else dispatchGoalP goalType
    | (``Not, #[p]) =>
        -- ¬P  is  P → False: introduce P, refute (integer leg, then ordered-field leg)
        withLocalDeclD `h p fun h => do (← proveFalseAny).mapM fun fp => mkLambdaFVars #[h] fp
    | _ => pure none

/-- The unifying decision tactic, instantiated at both the integer (`omega`) and
ordered-field (`linarith`, over `ℚ`) `Saturation` legs.  Closes a `False` goal, a
comparison goal over `ℤ` or `ℚ` (`≤`, `<`, `≥`, `>`, `=`), or the negation of one, from
the contradictory comparison hypotheses in context, by running the shared engine and
replaying its certificate into a kernel-checked proof.  The single boundary `throwError`
is the tactic-failure signal (a tactic must report when it cannot close the goal); all
internal error handling threads `Option`. -/
elab "kan_saturate" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    (← dispatchGoal (← goal.getType)).elim
      (throwError "kan_saturate: could not close the goal in the linear integer or ordered-field fragment")
      goal.assign

end Tactic
end KanSaturation
