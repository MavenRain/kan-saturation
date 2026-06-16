import KanSaturation.Core.Saturation

/-!
# `KanSaturation.Core.Engine`

The single **saturate → reduce → refute** algorithm, written once and parameterized
by `[Saturation F Cert]`.  This is the one place the unified procedure lives; the
three deciders differ only by their instance.  Mathlib-free and `MetaM`-free: it is
pure data flow, so the `Expr` bridging stays in the tactic layer.

The saturation step bound (`fuel`) is a placeholder for the genuine well-founded
measure (`Saturation.measure`); replacing the fuel cutoff with a measure-based
termination proof is part of the production-grade hardening (plan phase 6).
-/

namespace KanSaturation

/-- Why the engine stopped without producing a refutation. -/
inductive EngineError where
  /-- The fact set reached a fixpoint with no contradiction (the goal is not
      refutable in this fragment). -/
  | saturated
  /-- The fuel bound was exhausted before reaching a fixpoint. -/
  | exhausted
  deriving Repr, Inhabited, BEq

/-- Close `basis` under `consequences` (reducing every new fact to normal form),
checking for a refutation after each round, until a refutation, a fixpoint, or fuel
exhaustion.  Recursion is structural on `fuel`. -/
def saturate {F Cert : Type} [BEq F] [Saturation F Cert]
    (basis : Array F) (fuel : Nat) : Except EngineError Cert :=
  match Saturation.refuted? (Cert := Cert) basis with
  | some c => .ok c
  | none =>
    match fuel with
    | 0 => .error .exhausted
    | fuel + 1 =>
      let candidates : Array F :=
        basis.foldl (init := #[]) fun acc f =>
          acc ++ (Saturation.consequences (Cert := Cert) basis f).map
            (Saturation.reduce (Cert := Cert) basis)
      let fresh := candidates.filter fun g => !basis.contains g
      if fresh.isEmpty then
        .error .saturated
      else
        saturate (basis ++ fresh) fuel

/-- Run the engine on a starting fact set with a default fuel bound. -/
def run {F Cert : Type} [BEq F] [Saturation F Cert]
    (facts : Array F) (fuel : Nat := 1000) : Except EngineError Cert :=
  saturate facts fuel

end KanSaturation
