import KanSaturation.Core.Constraint
import KanSaturation.Core.Eval
import KanSaturation.Core.Reflect
import KanSaturation.Core.Collapse
import KanSaturation.Core.Engine
import KanSaturation.Instances.Integer
import KanSaturation.Tactic.Reify
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

deriving instance ToExpr for Rel
deriving instance ToExpr for LinForm
deriving instance ToExpr for Fact

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

/-- Collect the local hypotheses that are integer `≤` comparisons, as
`(lhs, rhs, proofExpr)` triples. -/
def collectLeHyps : MetaM (Array (Expr × Expr × Expr)) := do
  (← getLCtx).foldlM (init := #[]) fun acc decl => do
    if decl.isImplementationDetail then return acc
    match decl.type.getAppFnArgs with
    | (``LE.le, #[ty, _, a, b]) =>
        if ty.isConstOf ``Int then return acc.push (a, b, decl.toExpr) else return acc
    | _ => return acc

/-- The unifying decision tactic, instantiated at the integer `Saturation`.  Closes a
`False` goal from contradictory integer `≤` hypotheses by running the engine and
replaying its certificate into a kernel-checked proof. -/
elab "kan_saturate" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let hyps ← collectLeHyps
    -- pass 1: discover atoms (forms do not depend on env)
    let dummy ← buildEnv #[]
    let atoms ← hyps.foldlM (init := (#[] : Array Expr)) fun atoms hyp => do
      let (l, r, _) := hyp
      let (_, atoms) ← (reifyEvalProof dummy l).run atoms
      let (_, atoms) ← (reifyEvalProof dummy r).run atoms
      pure atoms
    let envExpr ← buildEnv atoms
    -- pass 2: build facts and `holds` proofs against the real env
    let init : Array (Fact × Expr) × Array Expr := (#[], atoms)
    let result ← hyps.foldlM (init := init) fun acc hyp => do
      let (fhs, atoms') := acc
      let (l, r, pf) := hyp
      let ((formL, pL), atoms'') ← (reifyEvalProof envExpr l).run atoms'
      let ((formR, pR), atoms''') ← (reifyEvalProof envExpr r).run atoms''
      let fact : Fact := { rel := .le, form := formR.add (formL.scale (-1)) }
      let holds := mkAppN (mkConst ``holds_le_of)
        #[envExpr, toExpr formL, toExpr formR, l, r, pL, pR, pf]
      pure (fhs.push (fact, holds), atoms''')
    let factsHolds := result.1
    let facts := (factsHolds.map (·.1)).toList
    let cert ← (Integer.solve facts).toOption.getDM
      (throwError "kan_saturate: no refutation in the linear integer fragment")
    -- fold the certificate combination: ∑ cᵢ · factᵢ, accumulating the proof
    let zeroForm : LinForm := { terms := [], const := 0 }
    let zeroProof := mkApp (mkConst ``Int.le_refl) (toExpr (0 : Int))
    let (foldedForm, foldedProof) ← cert.combo.foldlM
      (fun (acc : LinForm × Expr) (ci : Int × Nat) => do
        let (accForm, accProof) := acc
        let (c, idx) := ci
        let (fact, holds) ← (factsHolds[idx]?).getDM
          (throwError "kan_saturate: bad certificate index")
        let scaled := fact.form.scale c
        let cNonneg ← mkDecideProof (← mkAppM ``LE.le #[toExpr (0 : Int), toExpr c])
        let scaledProof := mkAppN (mkConst ``holds_le_scale)
          #[envExpr, toExpr c, toExpr fact.form, cNonneg, holds]
        let addProof := mkAppN (mkConst ``holds_le_add)
          #[envExpr, toExpr accForm, toExpr scaled, accProof, scaledProof]
        pure (accForm.add scaled, addProof))
      (zeroForm, zeroProof)
    -- close: the folded form is nonneg, collapses to all-zero terms, negative constant
    let collapseExpr ← mkAppM ``collapse #[toExpr foldedForm.terms]
    let allExpr ← mkAppM ``List.all #[collapseExpr, mkConst ``isZeroCoeff]
    let hCollapse ← mkDecideProof (← mkEq allExpr (toExpr true))
    let hneg ← mkDecideProof (← mkAppM ``LT.lt #[toExpr foldedForm.const, toExpr (0 : Int)])
    let falseProof := mkAppN (mkConst ``false_of_fold)
      #[envExpr, toExpr foldedForm, foldedProof, hCollapse, hneg]
    goal.assign falseProof

end Tactic
end KanSaturation
