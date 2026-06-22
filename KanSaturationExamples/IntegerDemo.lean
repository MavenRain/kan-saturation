import KanSaturation

/-!
# Integer leg data-level tests

Exercises the single `Engine` at the integer `Saturation` instance, at the level of
the internal constraint representation (the `Expr`-parsing tactic is a later phase).
Each `#guard` runs at elaboration: a failing check fails the build.
-/

namespace KanSaturationExamples.IntegerDemo

open KanSaturation
open KanSaturation.Integer

/-- Whether the engine produced a refutation certificate. -/
def ok? {ε α : Type} : Except ε α → Bool
  | .ok _    => true
  | .error _ => false

-- Constraints are `form rel 0`; variable `0` is `x`.
/-- `x ≥ 1`, i.e. `0 ≤ x - 1`. -/
def xGe1 : Fact := { rel := .le, form := { terms := [(1, 0)],  const := -1 } }
/-- `x ≤ 0`, i.e. `0 ≤ -x`. -/
def xLe0 : Fact := { rel := .le, form := { terms := [(-1, 0)], const := 0 } }
/-- `x ≥ 0`. -/
def xGe0 : Fact := { rel := .le, form := { terms := [(1, 0)],  const := 0 } }
/-- `x = 1`, i.e. `0 = x - 1`. -/
def xEq1 : Fact := { rel := .eq, form := { terms := [(1, 0)],  const := -1 } }
/-- `x = 2`, i.e. `0 = x - 2`. -/
def xEq2 : Fact := { rel := .eq, form := { terms := [(1, 0)],  const := -2 } }

-- Unsatisfiable systems are refuted (with a Farkas-style combination).
#guard ok? (solve [xGe1, xLe0])
#guard ok? (solve [xEq1, xEq2])

-- A satisfiable system is not refuted.
#guard !(ok? (solve [xGe0]))

/-! ## Termination on cyclic non-unit-coefficient systems (the Fourier-Motzkin rewrite).

The accumulate-only loop diverged on satisfiable cyclic systems with non-unit coefficients
(`2a ≤ b ∧ 2b ≤ a` generates unboundedly many growing-coefficient facts).  The
variable-elimination round terminates by the variable count, so these now decide in a
couple of rounds: the satisfiable cycle is *not* refuted (and returns), while adding the
lower bound that makes it infeasible *is* refuted. -/

/-- `2a ≤ b`, i.e. `0 ≤ b - 2a` (a = var 0, b = var 1). -/
def cyc2ab : Fact := { rel := .le, form := { terms := [(1, 1), (-2, 0)], const := 0 } }
/-- `2b ≤ a`, i.e. `0 ≤ a - 2b`. -/
def cyc2ba : Fact := { rel := .le, form := { terms := [(1, 0), (-2, 1)], const := 0 } }
/-- `1 ≤ a`, i.e. `0 ≤ a - 1`. -/
def aGe1 : Fact := { rel := .le, form := { terms := [(1, 0)], const := -1 } }

-- Satisfiable (a = b = 0): terminates and is not refuted.
#guard !(ok? (solve [cyc2ab, cyc2ba]))
-- Adding `1 ≤ a` makes the cycle integer-infeasible: refuted.
#guard ok? (solve [cyc2ab, cyc2ba, aGe1])

/-! ## End-to-end: `kan_saturate` closes real goals with a kernel-checked proof.

The single tactic, instantiated at the integer `Saturation`, refutes contradictory
linear-integer hypotheses (the `omega` fragment, recovered through the unified engine). -/

example (x : Int) (h₁ : 1 ≤ x) (h₂ : x ≤ 0) : False := by kan_saturate
example (x : Int) (h₁ : 2 ≤ x) (h₂ : x ≤ 1) : False := by kan_saturate
example (a b : Int) (h₁ : a + 1 ≤ b) (h₂ : b ≤ a) : False := by kan_saturate

/-- A named version of the headline refutation, so the produced proof term can be
audited: `#print axioms` below confirms it is axiom-clean (no `sorry`, no extra axioms
beyond what the kernel's `decide` reductions need). -/
theorem demo_refute (x : Int) (h₁ : 1 ≤ x) (h₂ : x ≤ 0) : False := by kan_saturate

#print axioms demo_refute

-- Extended reifier: subtraction, unary negation, and multiplication by a constant.
example (x : Int) (h₁ : 1 ≤ x - 1) (h₂ : x ≤ 1) : False := by kan_saturate
example (x : Int) (h₁ : 1 ≤ -x) (h₂ : 0 ≤ x) : False := by kan_saturate
example (x : Int) (h₁ : 2 * x ≤ 2) (h₂ : 2 ≤ x) : False := by kan_saturate
example (x : Int) (h₁ : x * 3 ≤ 3) (h₂ : 2 ≤ x) : False := by kan_saturate

/-! ## Strict, equality, and reversed comparison hypotheses.

`<`/`>` carry the integer strictness step `a < b ↔ a + 1 ≤ b`, so `0 < x < 1` is
refuted over ℤ (it is satisfiable over ℚ); `=` contributes both `≤` directions; `≥`/`>`
are the swapped duals. -/

example (x : Int) (h₁ : 0 < x) (h₂ : x < 1) : False := by kan_saturate
example (x : Int) (h₁ : x = 5) (h₂ : x ≤ 3) : False := by kan_saturate
example (x : Int) (h₁ : x ≥ 5) (h₂ : x ≤ 3) : False := by kan_saturate
example (x : Int) (h₁ : x > 5) (h₂ : x ≤ 5) : False := by kan_saturate

/-! ## Comparison goals, closed by negate-and-refute. -/

example (x : Int) (h : x ≤ 3) : x ≤ 5 := by kan_saturate
example (x : Int) (h : x ≤ 3) : x < 5 := by kan_saturate
example (x : Int) (h : 5 ≤ x) : x ≥ 3 := by kan_saturate
example (x : Int) (h : 5 ≤ x) : x > 3 := by kan_saturate
example (x : Int) (h₁ : x ≤ 5) (h₂ : 5 ≤ x) : x = 5 := by kan_saturate
example (x : Int) (h : x ≤ 3) : ¬ (5 ≤ x) := by kan_saturate

/-! ## Integer tightening: the ℤ/ℚ gap (`omega`, not `linarith`).

A constraint whose variable coefficients share a divisor `g` tightens by integer rounding:
`2x ≤ 1 ⟹ x ≤ 0` and `1 ≤ 2x ⟹ x ≥ 1` over `ℤ`, so `2x = 1` is refuted, though it is
*satisfiable* over `ℚ` (`x = 1/2`), where the ordered-field leg does not tighten.

The tightened constraint is a *sound* integer consequence (`Core.Tighten.holds_gcdTighten`),
so the tactic adds it to the engine's pool as an extra hypothesis: the shared Fourier-Motzkin
engine and the Farkas replay then close the goal with no change to the certificate.  (The
data-level `Integer.solve` runs pure rational FM, so this tightening is visible only through
the `kan_saturate` tactic, where the `holds` proofs are threaded.) -/

example (x : Int) (h : 2 * x = 1) : False := by kan_saturate
example (x : Int) (h₁ : 2 * x ≤ 1) (h₂ : 1 ≤ 2 * x) : False := by kan_saturate
example (x : Int) (h : 4 * x = 2) : False := by kan_saturate
example (x : Int) (h₁ : 0 < 2 * x) (h₂ : 2 * x < 2) : False := by kan_saturate

/-- A named tightening refutation, for the axiom audit below: kernel-checked, no `sorry`,
no `native_decide`. -/
theorem demo_tighten (x : Int) (h : 2 * x = 1) : False := by kan_saturate

#print axioms demo_tighten

/-! ## Multi-variable Fourier-Motzkin (variable elimination, including non-unit
coefficients).  Each goal eliminates its variables one per round and refutes on the residual
constant constraint; the satisfiable cousins (see the cyclic `#guard`s above) terminate by
the variable-count measure rather than chasing unbounded coefficient growth. -/

example (a b c : Int) (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : c < a) : False := by kan_saturate
example (a b c : Int) (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : c ≤ a - 1) : False := by kan_saturate
example (a b : Int) (h₁ : 2 * a ≤ b) (h₂ : 2 * b ≤ a) (h₃ : 1 ≤ a) : False := by kan_saturate
example (a b c : Int) (h₁ : 3*a ≤ b) (h₂ : 3*b ≤ c) (h₃ : 3*c ≤ a) (h₄ : 1 ≤ a) : False := by
  kan_saturate

end KanSaturationExamples.IntegerDemo
