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

/-! ## End-to-end: `kan_saturate` closes real goals with a kernel-checked proof.

The single tactic, instantiated at the integer `Saturation`, refutes contradictory
linear-integer hypotheses (the `omega` fragment, recovered through the unified engine). -/

example (x : Int) (h₁ : 1 ≤ x) (h₂ : x ≤ 0) : False := by kan_saturate
example (x : Int) (h₁ : 2 ≤ x) (h₂ : x ≤ 1) : False := by kan_saturate
example (a b : Int) (h₁ : a + 1 ≤ b) (h₂ : b ≤ a) : False := by kan_saturate

-- Extended reifier: subtraction, unary negation, and multiplication by a constant.
example (x : Int) (h₁ : 1 ≤ x - 1) (h₂ : x ≤ 1) : False := by kan_saturate
example (x : Int) (h₁ : 1 ≤ -x) (h₂ : 0 ≤ x) : False := by kan_saturate
example (x : Int) (h₁ : 2 * x ≤ 2) (h₂ : 2 ≤ x) : False := by kan_saturate
example (x : Int) (h₁ : x * 3 ≤ 3) (h₂ : 2 ≤ x) : False := by kan_saturate

end KanSaturationExamples.IntegerDemo
