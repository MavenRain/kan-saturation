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

All three legs are instances of **one generalized engine** (`Core.Saturation` +
`Core.Engine`): a single loop `refute → round → refute`, well-founded by a per-instance
`measure : Array F → Nat` that every productive `round` strictly decreases (a genuine
`termination_by`, not a fuel cutoff).  Two control structures realize `round`:

* **Variable elimination** (`Core.Eliminate`, the linear legs): eliminate one variable per
  round and drop every constraint mentioning it; the measure is the **variable count**, so
  termination is immediate, and cyclic non-unit-coefficient systems that diverged under the
  old accumulate loop (`2a ≤ b ∧ 2b ≤ a`) now decide in a couple of rounds.
* **Bounded accumulation** (`Core.Engine.accumulateRound`, the ideal leg): the Buchberger
  closure, never dropping a fact, bounded by a capacity measure.

Each leg carries a kernel-checked certificate replay (`#print axioms` clean, only
`propext`/`Classical.choice`/`Quot.sound`):

* **`Instances.Integer`** (`omega`): Fourier–Motzkin variable elimination + Farkas
  certificate over ℤ, plus **sound integer tightening** (`Core.Tighten`): a constraint whose
  variable coefficients share a divisor `g` rounds to `0 ≤ ∑(aᵢ/g)xᵢ + ⌊c/g⌋`, closing
  ℤ/ℚ-gap goals such as `2x = 1`.  Tightening is replayed at the tactic boundary as an extra
  *sound* hypothesis (`holds_gcdTighten`), so the shared engine and Farkas replay are
  unchanged.  This is the single-constraint GCD step; the Omega test's dark/grey-shadow
  splinter case-splits (which need a *branching* search) and `bmod` equality elimination
  remain the documented completeness frontier.
* **`Instances.OrderedField`** (`linarith`): the same variable elimination, un-tightened
  strict facts and **no** integrality tightening, over ℚ.
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
