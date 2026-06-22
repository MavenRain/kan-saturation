import KanSaturation.Core.Saturation
import KanTactics

/-!
# `KanSaturation.Core.Engine`

The single **saturate → reduce → refute** algorithm, written once and parameterized
by `[Saturation F Cert]`.  This is the one place the unified procedure lives; the
three deciders differ only by their instance.  Mathlib-free and `MetaM`-free: it is
pure data flow, so the `Expr` bridging stays in the tactic layer.

Termination is a **genuine well-founded recursion** on `Saturation.measure` (not a fuel
cutoff): every productive `round` returns its successor basis paired with a proof that
the measure strictly decreased, and `saturate` recurses `termination_by` that measure.
The linear legs make the measure the *variable count* (Fourier–Motzkin drops one variable
per round); the ideal leg uses the bounded `accumulateRound` capacity measure below.
-/

namespace KanSaturation

/-- Why the engine stopped without producing a refutation. -/
inductive EngineError where
  /-- The fact set reached a fixpoint with no contradiction (the goal is not
      refutable in this fragment). -/
  | saturated
  /-- A bounded accumulate round hit its capacity cap before reaching a fixpoint
      (retained so the linear and ideal legs share one error type; the well-founded
      loop itself never diverges). -/
  | exhausted
  deriving Repr, Inhabited, BEq

/-- The single generalized loop: refute, else take one `round`, else report a fixpoint.
Well-founded on `Saturation.measure`, discharged by the proof `round` carries. -/
def saturate {F Cert : Type} [Saturation F Cert] (basis : Array F) : Except EngineError Cert :=
  match Saturation.refuted? (Cert := Cert) basis with
  | some c => .ok c
  | none =>
    match Saturation.round (Cert := Cert) basis with
    | none => .error .saturated
    | some b' => saturate b'.val
  termination_by Saturation.measure (Cert := Cert) basis
  decreasing_by kan_exact b'.property

/-- Run the engine on a starting fact set. -/
def run {F Cert : Type} [Saturation F Cert] (facts : Array F) : Except EngineError Cert :=
  saturate facts

/-! ## The bounded accumulate round (the ideal leg's control structure)

The classic *closure* shape: superpose every fact against the basis, simplify, append the
non-redundant results, repeat until a fixpoint.  It never drops facts, so it has no
intrinsic variable-count measure; instead it is bounded by a **capacity** cap, and the
well-founded measure is the remaining capacity `cap + 1 - basis.size`, which strictly
decreases because each productive round adds at least one fresh fact.  A refused fact can
only cost a refutation (incompleteness), never fabricate one, so the cap is sound. -/

/-- The basis-size capacity cap.  Per round costs roughly `basis²`, so it is kept small to
bound a single round, not just the round count; realistic problems refute or saturate far
below it. -/
def cap : Nat := 128

/-- The remaining-capacity measure for the accumulate round. -/
def capMeasure {F : Type} (basis : Array F) : Nat := cap + 1 - basis.size

/-- One accumulate round, given the per-instance `step` (superpose-then-simplify): stop at
the capacity cap or at a fixpoint, otherwise append the fresh, non-duplicate consequences.
The result carries the proof that `capMeasure` strictly decreased. -/
def accumulateRound {F : Type} [BEq F] (step : Array F → Array F) (basis : Array F) :
    Option { basis' : Array F // capMeasure basis' < capMeasure basis } :=
  if hb : basis.size ≤ cap then
    let fresh := (step basis).filter fun g => !basis.contains g
    match hf : fresh.size with
    | 0 => none
    | n + 1 =>
        some ⟨basis ++ fresh, by
          kan_exact (((Array.size_append (xs := basis) (ys := fresh)) ▸
            (Nat.sub_lt_sub_left (Nat.lt_succ_of_le hb)
              (Nat.lt_add_of_pos_right (k := fresh.size) (hf ▸ Nat.succ_pos n)))) :
            cap + 1 - (basis ++ fresh).size < cap + 1 - basis.size)⟩
  else
    none

end KanSaturation
