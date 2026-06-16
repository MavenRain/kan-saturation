-- Categorical + tactic foundation (kan-tactics transitively brings comp-cat-theory).
import KanTactics

-- Core framework: the one engine and the interface it runs on.
import KanSaturation.Core.Constraint
import KanSaturation.Core.Saturation
import KanSaturation.Core.Engine
import KanSaturation.Core.Eval
import KanSaturation.Core.Reflect

-- Instances: the deciders recovered as instances of the one engine.
import KanSaturation.Instances.Integer

-- Tactic layer: reification of Lean goals into the internal representation.
import KanSaturation.Tactic.Reify

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

## Layout (built up over the phases in the plan)

* `KanSaturation.Core.Constraint`  — own datatypes over core ℤ/ℚ
* `KanSaturation.Core.Saturation`  — the unifying-completeness interface
* `KanSaturation.Core.Engine`      — the one saturate→reduce→refute algorithm
* `KanSaturation.Core.Certificate` — certificate replay into a checked proof
* `KanSaturation.Reflector`        — the saturation Kan extension via `adjToLan`
* `KanSaturation.Tactic.Saturate`  — the single tactic `kan_saturate`
* `KanSaturation.Instances.*`      — omega / linarith / polyrith as instances
-/
