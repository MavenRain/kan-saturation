import KanSaturation.Core.Constraint
import Lean

/-!
# `KanSaturation.Tactic.Reify`

The reification half of the tactic layer: parse a Lean `Expr` describing a linear
integer (in)equality into the internal `Fact` representation, interning atomic
subterms (free variables, opaque terms) as `Var` indices.

This is meta-programming on `Expr` (exempt from the kan-tactics-only rule, exactly as
`kan-tactics`' own elaborators are), Mathlib-free, and total/`Option`-returning: a
shape it cannot linearize yields `none` rather than an error.  The certificate replay
that turns an engine refutation into a kernel-checked proof, and the `kan_saturate`
elaborator that drives both, build on this in `KanSaturation.Tactic.Saturate`.
-/

namespace KanSaturation
namespace Tactic

open Lean Lean.Meta

/-- Intern an atomic subterm, returning its variable index (its position in the atom
array; appended if new). -/
def internAtom (e : Expr) : StateT (Array Expr) MetaM Var := do
  let atoms ← get
  match atoms.findIdx? (· == e) with
  | some i => pure i
  | none   => set (atoms.push e); pure atoms.size

/-- Parse an integer expression into a `LinForm`, interning non-linear atoms.  Returns
`none` only on a genuinely non-linear shape (a product of two non-constant factors).
Recursion is on the expression structure (hence `partial`). -/
partial def parseLinForm (e : Expr) : StateT (Array Expr) MetaM (Option LinForm) := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
      let some fa ← parseLinForm a | pure none
      let some fb ← parseLinForm b | pure none
      pure (some (fa.add fb))
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
      let some fa ← parseLinForm a | pure none
      let some fb ← parseLinForm b | pure none
      pure (some (fa.add (fb.scale (-1))))
  | (``Neg.neg, #[_, _, a]) =>
      let some fa ← parseLinForm a | pure none
      pure (some (fa.scale (-1)))
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
      let some fa ← parseLinForm a | pure none
      let some fb ← parseLinForm b | pure none
      if fa.terms.isEmpty then
        pure (some (fb.scale fa.const))
      else if fb.terms.isEmpty then
        pure (some (fa.scale fb.const))
      else
        pure none
  | (``OfNat.ofNat, #[_, n, _]) =>
      match n.nat? with
      | some k => pure (some { terms := [], const := Int.ofNat k })
      | none   => let v ← internAtom e; pure (some { terms := [(1, v)], const := 0 })
  | _ =>
      let v ← internAtom e
      pure (some { terms := [(1, v)], const := 0 })

/-- Parse a `Prop` that is a linear integer comparison into a `Fact` of the form
`0 rel form`.  Handles `≤`, `<`, `≥`, `>`, and `=` over `Int`; returns `none`
otherwise. -/
partial def parseFact (e : Expr) : StateT (Array Expr) MetaM (Option Fact) := do
  match e.getAppFnArgs with
  | (``LE.le, #[ty, _, a, b]) =>
      if ty.isConstOf ``Int then
        let some fa ← parseLinForm a | pure none
        let some fb ← parseLinForm b | pure none
        pure (some { rel := .le, form := fb.add (fa.scale (-1)) })  -- 0 ≤ b - a
      else pure none
  | (``LT.lt, #[ty, _, a, b]) =>
      if ty.isConstOf ``Int then
        let some fa ← parseLinForm a | pure none
        let some fb ← parseLinForm b | pure none
        pure (some { rel := .lt, form := fb.add (fa.scale (-1)) })  -- 0 < b - a
      else pure none
  | (``GE.ge, #[ty, _, a, b]) =>
      if ty.isConstOf ``Int then
        let some fa ← parseLinForm a | pure none
        let some fb ← parseLinForm b | pure none
        pure (some { rel := .le, form := fa.add (fb.scale (-1)) })  -- a ≥ b → 0 ≤ a - b
      else pure none
  | (``GT.gt, #[ty, _, a, b]) =>
      if ty.isConstOf ``Int then
        let some fa ← parseLinForm a | pure none
        let some fb ← parseLinForm b | pure none
        pure (some { rel := .lt, form := fa.add (fb.scale (-1)) })  -- a > b → 0 < a - b
      else pure none
  | (``Eq, #[ty, a, b]) =>
      if ty.isConstOf ``Int then
        let some fa ← parseLinForm a | pure none
        let some fb ← parseLinForm b | pure none
        pure (some { rel := .eq, form := fb.add (fa.scale (-1)) })  -- b - a = 0
      else pure none
  | _ => pure none

end Tactic
end KanSaturation
