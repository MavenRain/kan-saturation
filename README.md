# kan-saturation

A **Mathlib-free** Lean 4 library that realizes the *unifying completeness theorem*
behind `omega`, `linarith`, and `polyrith` as a **single algorithm**, surfaces it as
one tactic `kan_saturate`, and uses it to construct the corresponding **saturation
Kan extension**.

## The idea

The three deciders share one shape:

> **saturate** the constraint cone-plus-ideal to its closure, **reduce** to a normal
> form, then **check** the contradiction witness (`-1` in the closure, `0 < 0`, or an
> empty residue).

The search (Buchberger superposition / Fourier-Motzkin bound-combination / integer
tightening) *computes a reflector*; the reduction *applies it*. This library writes
that saturate-then-reduce engine **once** and recovers the three deciders as the three
`Saturation` instances of the one tactic.

The *unifying completeness theorem* ("the saturation closure is tight", i.e.
quantifier elimination / having a model companion) is the hypothesis under which the
saturated objects are reflective; the reflector is then a **left Kan extension**, built
with `comp-cat-theory`'s `adjToLan`. Soundness of `kan_saturate` rests on per-call,
kernel-checked certificates, **not** on that theorem, which is why the entire stack
stays Mathlib-free:

```
comp-cat-theory  →  kan-tactics  →  kan-saturation
```

over core `Int` / `Nat` / `Rat` and the library's own polynomial/constraint datatypes.

## Tightness legs: proven vs assumed

| Instance | Decider recovered | Tightness theorem | Status |
| --- | --- | --- | --- |
| `Instances.Integer` | `omega` | Presburger completeness / Chvátal-Gomory | stated, axiomatized (Presburger 1929; Gomory-Chvátal) |
| `Instances.OrderedField` | `linarith` | Farkas / LP duality | stated, proven in-house where tractable (Farkas 1902) |
| `Instances.Ideal` | `polyrith` | Hilbert Nullstellensatz | stated, axiomatized (Hilbert 1893) |

`tight` is documented per instance and is **not load-bearing for soundness**.

## Use

```lean
-- in your lakefile.lean
require «kan-saturation» from "../kan-saturation"
```

Then `import KanSaturation` and use `kan_saturate` on integer, rational, or
polynomial-ideal goals over core carriers.

## Conventions

All proof scripts use **kan-tactics only** (never `simp`/`rw`/`ring`/`omega`/`linarith`);
the engine and tactic elaborator are meta-programming and are exempt. No exceptions
(`Option`/`Except`, never `panic!`/`throw`). Reusable reservoir-style dependency.
