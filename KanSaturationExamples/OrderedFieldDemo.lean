import KanSaturation

/-!
# Ordered-field leg (`linarith`) demonstration

Exercises the ordered-field `Saturation` leg over `ℚ`: the same engine as the integer
leg, but fed *un-tightened* strict facts and interpreted over an ordered field.  Each
`#guard` runs at elaboration; each `example` produces a kernel-checked proof.

The headline is the **`omega` vs `linarith` contrast**: `0 < x ∧ x < 1` is refutable
over `ℤ` (no integer strictly between `0` and `1`) but *satisfiable* over `ℚ`
(e.g. `x = 1/2`), so the integer leg refutes it and the ordered-field leg does not — from
one engine, differing only in whether strict inequalities are tightened.
-/

namespace KanSaturationExamples.OrderedFieldDemo

open KanSaturation
open KanSaturation.OrderedField

/-- Whether the engine produced a refutation certificate. -/
def ok? {ε α : Type} : Except ε α → Bool
  | .ok _    => true
  | .error _ => false

/-! ## Data level: the `omega`/`linarith` contrast on `0 < x ∧ x < 1`.

Variable `0` is `x`.  Strict facts enter the ordered-field engine as genuine `lt`
(no `a < b ↦ a + 1 ≤ b` tightening). -/

/-- `0 < x`. -/
def xPos : Fact := { rel := .lt, form := { terms := [(1, 0)],  const := 0 } }
/-- `0 < 1 - x`  (i.e. `x < 1`). -/
def xLt1 : Fact := { rel := .lt, form := { terms := [(-1, 0)], const := 1 } }
/-- `0 ≤ -x`  (i.e. `x ≤ 0`). -/
def xLe0 : Fact := { rel := .le, form := { terms := [(-1, 0)], const := 0 } }

-- Over ℚ, `0 < x ∧ x < 1` is satisfiable, so the ordered-field engine does NOT refute it…
#guard !(ok? (OrderedField.solve [xPos, xLt1]))
-- …whereas the integer engine, which tightens `<`, DOES refute the same system (`omega`).
#guard ok? (Integer.solve [{ rel := .le, form := { terms := [(1, 0)],  const := -1 } },
                           { rel := .le, form := { terms := [(-1, 0)], const := 0 } }])
-- A genuinely contradictory strict ℚ system (`0 < x ∧ x ≤ 0`) IS refuted (Farkas).
#guard ok? (OrderedField.solve [xPos, xLe0])

/-! ## End-to-end: `kan_saturate` closes real `ℚ` goals with a kernel-checked proof.

Contradictory rational hypotheses are refuted by the unified engine through the
ordered-field leg (the `linarith` fragment). -/

-- Integer-coefficient rational refutations (Farkas over ℚ); literal coefficient on
-- either side of the variable.
example (x : Rat) (h₁ : 2 * x ≤ 3) (h₂ : 2 ≤ x) : False := by kan_saturate
example (x : Rat) (h₁ : x * 3 ≤ 3) (h₂ : 2 ≤ x) : False := by kan_saturate
example (a b : Rat) (h₁ : a + b ≤ 1) (h₂ : 1 < a) (h₃ : 0 ≤ b) : False := by kan_saturate

-- Strict inequalities stay strict and still refute genuine contradictions.
example (a b c : Rat) (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : c < a) : False := by kan_saturate

-- Equality hypotheses contribute both `≤` directions.
example (x : Rat) (h₁ : x = 5) (h₂ : x ≤ 3) : False := by kan_saturate

/-- A named rational refutation, so the produced term can be audited as axiom-clean. -/
theorem demo_refute_q (x : Rat) (h₁ : 2 * x ≤ 3) (h₂ : 2 ≤ x) : False := by kan_saturate

#print axioms demo_refute_q

/-! ## Denominator clearing: fractional coefficients are cleared to integer ones.

`x / 2 ≤ 1` is reified by scaling through the denominator (`x ≤ 2`), so the engine still
sees only integer-coefficient constraints. -/

example (x : Rat) (h₁ : x / 2 ≤ 1) (h₂ : 3 ≤ x) : False := by kan_saturate
example (x : Rat) (h₁ : x / 3 ≤ 1) (h₂ : 4 ≤ x) : False := by kan_saturate

/-- A named denominator-clearing refutation, audited below. -/
theorem demo_div_q (x : Rat) (h₁ : x / 2 ≤ 1) (h₂ : 3 ≤ x) : False := by kan_saturate

#print axioms demo_div_q

/-! ## Comparison goals over `ℚ`, closed by negate-and-refute. -/

example (x : Rat) (h : x ≤ 3) : x ≤ 5 := by kan_saturate
example (x : Rat) (h : x ≤ 3) : x < 5 := by kan_saturate
example (x : Rat) (h : 5 ≤ x) : x ≥ 3 := by kan_saturate
example (x : Rat) (h : 5 ≤ x) : x > 3 := by kan_saturate
example (x : Rat) (h₁ : x ≤ 5) (h₂ : 5 ≤ x) : x = 5 := by kan_saturate
example (x : Rat) (h : x ≤ 3) : ¬ (5 ≤ x) := by kan_saturate

/-! ## Multi-variable Fourier-Motzkin over `ℚ` (several elimination rounds). -/

example (a b c : Rat) (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : c ≤ a - 1) : False := by kan_saturate
example (a b : Rat) (h₁ : 2 * a ≤ b) (h₂ : 2 * b ≤ a) (h₃ : 1 ≤ a) : False := by kan_saturate

end KanSaturationExamples.OrderedFieldDemo
