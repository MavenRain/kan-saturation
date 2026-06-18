-- Categorical + tactic foundation (kan-tactics transitively brings comp-cat-theory).
import KanTactics

-- Core framework: the one engine and the interface it runs on.
import KanSaturation.Core.Constraint
import KanSaturation.Core.Saturation
import KanSaturation.Core.Engine
import KanSaturation.Core.Eval
import KanSaturation.Core.Reflect
import KanSaturation.Core.Collapse
import KanSaturation.Core.OrderedField

-- Instances: the deciders recovered as instances of the one engine.
import KanSaturation.Instances.Integer
import KanSaturation.Instances.OrderedField
import KanSaturation.Instances.Ideal

-- Tactic layer: reification of Lean goals, and the verified reifier for replay.
import KanSaturation.Tactic.Reify
import KanSaturation.Tactic.SaturateIdeal
import KanSaturation.Tactic.Saturate

/-!
# kan-saturation

A Mathlib-free Lean 4 library realizing the *unifying completeness theorem* for
linear and polynomial decision procedures as a single algorithm, and deriving
the corresponding *saturation Kan extension* from it.

## Thesis

`omega`, `linarith`, and `polyrith` share one shape: **saturate** the constraint
cone-plus-ideal to its closure, **reduce** to a normal form, then **check** the
contradiction witness (`-1` in the closure, `0 < 0`, or an empty residue).  The
search computes a reflector; the reduction applies it.  This library writes that
saturate-then-reduce engine *once* (`KanSaturation.Core.Engine`), parameterized by
a `Saturation` instance, and recovers the three deciders as the three instances of
the one tactic `kan_saturate`.

The *unifying completeness theorem* ("the saturation closure is tight") is the
hypothesis under which the saturated objects are reflective; the reflector is then
a left Kan extension (`KanSaturation.Reflector`), built with `comp-cat-theory`'s
`adjToLan`.  Soundness of the tactic rests on per-call kernel-checked certificates,
not on that theorem, so the whole stack stays Mathlib-free:
`comp-cat-theory → kan-tactics → kan-saturation`, over core `Int`/`Nat`/`Rat`.

## Layout

* `KanSaturation.Core.Constraint`   — linear datatypes over core ℤ/ℚ
* `KanSaturation.Core.Saturation`   — the unifying-completeness interface
* `KanSaturation.Core.Engine`       — the one saturate→reduce→refute algorithm
* `KanSaturation.Core.Eval`/`Collapse` — linear eval + collection soundness lemmas
* `KanSaturation.Core.OrderedField` — the ordered-field carrier + ℚ Farkas soundness
* `KanSaturation.Core.PolyReflect`  — multivariate-polynomial datatypes + ℚ ideal soundness
* `KanSaturation.Instances.{Integer,OrderedField,Ideal}` — omega / linarith / polyrith
* `KanSaturation.Tactic.{Saturate,SaturateField,SaturateIdeal}` — the `kan_saturate` legs
  (ℤ, ℚ-linear, and ℚ-polynomial-ideal), each replaying a kernel-checked certificate

The *saturation Kan extension* itself (`Lan` via `comp-cat-theory`'s `adjToLan`, the
categorical capstone the thesis names) is the planned next module; the three deciders and
their certificate replays above are complete.
-/
