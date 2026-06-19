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
saturated objects are reflective; `comp-cat-theory`'s `adjToLan` then realizes the
inclusion of the saturated subcategory as a **left Kan extension** of the identity
along saturation (dually, `adjToRan` exhibits saturation itself as the matching right
Kan extension). Soundness of `kan_saturate` rests on per-call,
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

## Implementation status

All three legs are implemented as instances of the one engine, each with a kernel-checked
certificate replay (`#print axioms` clean, only `propext`/`Classical.choice`/`Quot.sound`):

* **`Instances.Integer`** (`omega`): Fourier–Motzkin + Farkas certificate, over ℤ.
* **`Instances.OrderedField`** (`linarith`): the same engine, un-tightened strict facts, over ℚ.
* **`Instances.Ideal`** (`polyrith`): Buchberger superposition with cofactor provenance over
  ℚ; closes both *refutation* goals (a nonzero constant in `⟨hyps⟩`, a Nullstellensatz
  witness ⇒ `False`) and *equality* goals (`a = b` reduced to ideal membership `a − b ∈
  ⟨hyps⟩`). First cut: a sound Buchberger core whose cofactor replay cancels monomials by
  their raw (concatenated) exponent vectors, so it closes certificates already in aligned
  raw form; cross-variable monomial reordering and full Gröbner completeness are deferred.
  Soundness is the kernel-checked replay and is independent of these completeness caps.

The **categorical capstone** is implemented too:

* **`Reflector`** is the *saturation Kan extension*.  A preorder is a thin category, so
  saturation-as-a-closure-operator on the entailment preorder is left adjoint to the
  inclusion of its fixed points (the saturated configurations).  `comp-cat-theory`'s
  `adjToLan` turns that reflection into a genuine left Kan extension `include' =
  Lan_saturate (Id)`, and `adjToRan` gives the dual `saturate = Ran_include' (Id)`.  The
  three closure laws are exactly the per-instance tightness theorem, so they enter as the
  `Closure` interface rather than as assumptions on soundness; a worked `Bool` instance
  ("saturate to ⊤") witnesses the whole pipeline with `#print axioms` showing only
  `propext`.

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
