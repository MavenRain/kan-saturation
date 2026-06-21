import KanSaturation

/-!
# Saturation Kan extension demo

Exercises the categorical capstone (`KanSaturation.Reflector`) at the level the rest of
this target works: small definitional facts checked at elaboration.  The point of the
capstone is that *the inclusion of the saturated subcategory is literally the left Kan
extension of the identity along saturation*, so the Lan's underlying functor **is** the
inclusion, and dually the Ran's underlying functor **is** saturation.  Each `example`
below makes that identification, and it holds by `rfl`.

Worked at the `Bool` "saturate to ⊤" instance, which is `#print axioms`-clean (`propext`).
-/

namespace KanSaturationExamples.ReflectorDemo

open CompCatTheory
open KanSaturation.Reflector

/-- The left Kan extension's functor is exactly the inclusion of saturated objects:
`include' = Lan_saturate (Id)` at the level of the underlying functor. -/
example : (Example.satToTopLan).functor = include' Bool := by kan_rfl

/-- The Lan unit is the reflection unit (the inflationary map `x ⟶ cl x`). -/
example : (Example.satToTopLan).unit = (reflection Bool).unit := by kan_rfl

/-- Dually, the right Kan extension's functor is exactly saturation:
`saturate = Ran_include' (Id)`. -/
example : (Example.satToTopRan).functor = saturate Bool := by kan_rfl

/-- And the Ran counit is the reflection counit. -/
example : (Example.satToTopRan).counit = (reflection Bool).counit := by kan_rfl

end KanSaturationExamples.ReflectorDemo
