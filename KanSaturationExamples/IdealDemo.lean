import KanSaturation

/-!
# Ideal leg (`polyrith`) demonstration

Exercises the ideal `Saturation` leg over `ℚ`: Buchberger superposition with cofactor
provenance, recovering the `polyrith` direction.  Two replays are on show:

* **Refutation** (`proveFalseP`): contradictory polynomial equalities (`x*x = 2` and
  `x*x = 3`) put a *nonzero constant* in the ideal — a Nullstellensatz `1 ∈ ⟨hyps⟩`
  witness — which the tactic replays into a kernel-checked proof of `False`.
* **Membership** (`dispatchGoalP`): a polynomial equality goal (`x*x*x = x*y`) that lies
  in the ideal of the hypotheses (`x*x = y`) is closed by reducing the goal polynomial to
  `0` modulo the generators and replaying the cofactor representation.

The key contrast with the other legs is that products are reified *exactly* (recursing
into both factors), so genuinely nonlinear hypotheses are first-class here.  Each `#guard`
runs at elaboration; each `example` produces a kernel-checked proof.

First-cut scope: the cofactor replay cancels monomials by their *raw* (unsorted,
concatenated) exponent vectors, so a refutation/membership closes when the certificate's
cofactor products land on monomials already in aligned raw form — which the examples below
do (shared products such as `x*x`, `x*y`, and the membership multiple `x·(x*x − y)`).
Certificates that would need cross-variable monomial reordering (`x = y` then `x*x` vs
`y*y`) are outside this first cut and `kan_saturate` simply declines them.
-/

namespace KanSaturationExamples.IdealDemo

open KanSaturation
open KanSaturation.Ideal

/-- Whether the engine produced a refutation certificate. -/
def ok? {ε α : Type} : Except ε α → Bool
  | .ok _    => true
  | .error _ => false

/-! ## Data level: `Ideal.solve` / `Ideal.member?` directly.

Variable `0` is `x`, variable `1` is `y`.  Monomials are `⟨coeff, exponent-vector⟩`. -/

/-- `x*x - 2` (i.e. the generator `x*x = 2`). -/
def xx2 : MvPoly := ⟨[⟨1, [(0, 1), (0, 1)]⟩, ⟨-2, []⟩]⟩
/-- `x*x - 3` (i.e. the generator `x*x = 3`). -/
def xx3 : MvPoly := ⟨[⟨1, [(0, 1), (0, 1)]⟩, ⟨-3, []⟩]⟩
/-- `x*x - y` (i.e. the generator `x*x = y`). -/
def xxy : MvPoly := ⟨[⟨1, [(0, 1), (0, 1)]⟩, ⟨-1, [(1, 1)]⟩]⟩
/-- The goal difference `x*x*x - x*y` (i.e. the goal `x*x*x = x*y`). -/
def goalEq : MvPoly := ⟨[⟨1, [(0, 1), (0, 1), (0, 1)]⟩, ⟨-1, [(0, 1), (1, 1)]⟩]⟩

-- `x*x = 2 ∧ x*x = 3` is infeasible: a nonzero constant lies in the ideal.
#guard ok? (Ideal.solve [xx2, xx3])
-- A single generator is satisfiable, so no nonzero constant is derived.
#guard !(ok? (Ideal.solve [xx2]))
-- `x*x*x - x*y` lies in `⟨x*x - y⟩` (multiply the generator by `x`): membership succeeds.
#guard (Ideal.member? [xxy] goalEq).isSome
-- A polynomial not in the ideal: membership fails.
#guard (Ideal.member? [xxy] (MvPoly.const 1)).isNone

/-! ## End-to-end: `kan_saturate` closes real `ℚ` goals with a kernel-checked proof. -/

-- Refutation: contradictory nonlinear equalities (Nullstellensatz over ℚ).
example (x : Rat) (h₁ : x * x = 2) (h₂ : x * x = 3) : False := by kan_saturate

/-- A named nonlinear refutation, audited below. -/
theorem demo_ideal_false (x : Rat) (h₁ : x * x = 2) (h₂ : x * x = 3) : False := by kan_saturate

#print axioms demo_ideal_false

-- Membership: a nonlinear equality goal lying in the ideal of the hypotheses.
example (x y : Rat) (h : x * x = y) : x * x * x = x * y := by kan_saturate

/-- A named ideal-membership equality, audited below. -/
theorem demo_ideal_eq (x y : Rat) (h : x * x = y) : x * x * x = x * y := by kan_saturate

#print axioms demo_ideal_eq

-- A further multi-variable infeasible system: `x*y = 2 ∧ x*y = 3` puts the nonzero
-- constant `1` in the ideal (Nullstellensatz over the shared product `x*y`).
example (x y : Rat) (h₁ : x * y = 2) (h₂ : x * y = 3) : False := by kan_saturate

end KanSaturationExamples.IdealDemo
