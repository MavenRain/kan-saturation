import KanSaturation.Core.Constraint
import KanSaturation.Core.Eval
import KanSaturation.Core.Reflect
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

Scope (this part): `+`, integer literals, and atoms, with any other shape interned as
an opaque atom (sound; richer shapes such as `*` and `-` are added later).
-/

open Lean Lean.Meta

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

/-- Verified reification: returns `(f, proof : e = f.eval env)`, interning atoms. -/
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
  | (``OfNat.ofNat, #[_, n, _]) =>
      if let .lit (.natVal k) := n then
        let c : Int := Int.ofNat k
        let f : LinForm := { terms := [], const := c }
        let lem := mkApp2 (mkConst ``LinForm.eval_const) envExpr (toExpr c)
        pure (f, ← mkEqSymm lem)
      else
        reifyAtom envExpr e
  | _ => reifyAtom envExpr e

end Tactic
end KanSaturation
