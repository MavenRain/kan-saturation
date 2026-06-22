import KanSaturation.Core.Constraint
import KanSaturation.Core.Saturation
import KanSaturation.Core.Engine
import KanSaturation.Core.Eliminate
import KanSaturation.Core.OrderedField
import KanSaturation.Instances.Integer

/-!
# `KanSaturation.Instances.OrderedField`

The ordered-field leg: `linarith` recovered as a `Saturation` instance, with `ℚ` (core
`Rat`) as the flagship carrier (`instance : OrderedField Rat`).

## One engine, two deciders

The saturation step is **rational Fourier-Motzkin variable elimination** with
nonnegative-combination provenance, exactly the integer leg's `eliminateVar`
(`Instances.Integer`, via `Core.Eliminate`).  This module therefore *delegates* its
`eliminateVar`/`refuted?` to that engine rather than duplicating it, keeping a single
source of truth for the algorithm (the library thesis: one engine, recovered as
instances).  The ordered-field leg is nonetheless a **distinct** `Saturation` instance
over its own `DFact`, because the legs diverge in two ways:

* **Reification (tactic layer).** `omega` tightens `a < b` to `a + 1 ≤ b` using
  integrality; `linarith` keeps `<` strict.  Feeding *un-tightened* strict facts to the
  shared engine is what makes `0 < x ∧ x < 1` saturate without refutation over `ℚ`
  (it is satisfiable there) while `omega` refutes it over `ℤ`.
* **Tightness (soundness carrier).** The integer leg is sound over `ℤ`; this leg is
  sound over any `OrderedField` (`Core.OrderedField`), with the certificate replayed
  through the field soundness lemmas at `ℚ`.

The integer leg's *integrality tightening* (`Core.Tighten`, replayed at the tactic
boundary) is precisely what this leg omits: delegating only to `eliminateVar` keeps the
ordered-field step pure rational FM, so rational-satisfiable systems stay unrefuted.

The *tightness theorem* for this leg is **Farkas' lemma / LP duality** (every
infeasible rational system has a nonnegative-combination certificate of `0 < 0`); as in
the integer leg it is documented, not load-bearing for soundness, which rests on the
per-call kernel-checked replay.
-/

namespace KanSaturation

/-- `ℚ` (core `Rat`) as the flagship `OrderedField`.  Every field is a core `Rat.*`
lemma (no Mathlib, no `grind` internals), so the instance is immediate; the iff-shaped
core lemmas contribute their forward or backward direction. -/
instance : OrderedField Rat where
  add_comm := Rat.add_comm
  add_assoc := Rat.add_assoc
  zero_add := Rat.zero_add
  add_zero := Rat.add_zero
  neg_add_cancel := Rat.neg_add_cancel
  mul_assoc := Rat.mul_assoc
  mul_comm := Rat.mul_comm
  one_mul := Rat.one_mul
  mul_zero := Rat.mul_zero
  mul_add := Rat.mul_add
  sub_eq_add_neg := Rat.sub_eq_add_neg
  mul_inv_cancel := Rat.mul_inv_cancel
  div_mul_cancel := fun _ _ => Rat.div_mul_cancel
  intCast_zero := Rat.intCast_zero
  intCast_one := Rat.intCast_one
  intCast_add := Rat.intCast_add
  intCast_mul := Rat.intCast_mul
  intCast_neg := Rat.intCast_neg
  le_refl := fun _ => Rat.le_refl
  le_trans := fun _ _ _ => Rat.le_trans
  le_antisymm := fun _ _ => Rat.le_antisymm
  le_of_lt := fun _ _ => Rat.le_of_lt
  lt_irrefl := fun _ => Rat.lt_irrefl
  lt_iff_le_and_ne := fun _ _ => Rat.lt_iff_le_and_ne
  not_le := fun _ _ => Rat.not_le
  add_le_add_left := fun _ _ _ h => Rat.add_le_add_left.mpr h
  add_lt_add_left := fun _ _ _ h => Rat.add_lt_add_left.mpr h
  mul_nonneg := fun _ _ => Rat.mul_nonneg
  mul_pos := fun _ _ => Rat.mul_pos
  mul_le_mul_of_nonneg_left := fun _ _ _ => Rat.mul_le_mul_of_nonneg_left
  mul_lt_mul_of_pos_left := fun _ _ _ => Rat.mul_lt_mul_of_pos_left
  intCast_nonneg := fun _ => Rat.intCast_nonneg.mpr
  intCast_pos := fun _ => Rat.intCast_pos.mpr
  intCast_le := fun _ _ => Rat.intCast_le_intCast.mpr
  intCast_lt := fun _ _ => Rat.intCast_lt_intCast.mpr
  intCast_inj := fun _ _ => Rat.intCast_inj.mp

namespace OrderedField

/-- A derived fact for the ordered-field leg: a constraint with its
nonnegative-combination provenance.  Structurally identical to `Integer.DFact`, kept as
a distinct type so this is a genuinely distinct `Saturation` instance (the legs diverge
once the integer leg gains integrality tightening; see the module note). -/
structure DFact where
  /-- The constraint `form rel 0`. -/
  fact  : Fact
  /-- Provenance: `∑ cᵢ · hypᵢ`, as `(coefficient, hypothesis-index)` pairs. -/
  combo : List (Int × Nat)
  deriving Repr, Inhabited

/-- View as an integer-leg derived fact (for delegating the shared FM step). -/
def DFact.toInt (d : DFact) : Integer.DFact := { fact := d.fact, combo := d.combo }

/-- Recover from an integer-leg derived fact. -/
def DFact.ofInt (d : Integer.DFact) : DFact := { fact := d.fact, combo := d.combo }

/-- The refutation certificate type is shared with the integer leg. -/
abbrev Cert := Integer.Cert

/-- Logical equality up to positive scaling and term order (mirrors `Integer.DFact`), so
the saturation loop deduplicates scalar multiples and reaches a fixpoint. -/
instance : BEq DFact where
  beq a b := a.fact.rel == b.fact.rel && a.fact.form.key == b.fact.form.key

/-- Eliminate `v` by the integer leg's *pure* rational Fourier-Motzkin, through the
`toInt`/`ofInt` view.  No strict tightening (strict facts entered as genuine `lt`, which
`resolve`/`refuted?` propagate) and, the soundness-carrying difference, **no integrality
tightening**: this leg delegates only to the rational elimination, so rational-satisfiable
systems (e.g. `0 < x ∧ x < 1` over `ℚ`) stay unrefuted where the integer leg would tighten
them to a contradiction. -/
def eliminateVar (v : Var) (facts : Array DFact) : Array DFact :=
  (Integer.eliminateVar v (facts.map DFact.toInt)).map DFact.ofInt

/-- Detect a derived constant-false fact, delegated to the shared engine. -/
def refuted? (basis : Array DFact) : Option Cert :=
  Integer.refuted? (basis.map DFact.toInt)

/-- The elimination schedule, delegated to the integer leg's `allVars`. -/
def allVars (facts : Array DFact) : List Var :=
  Integer.allVars (facts.map DFact.toInt)

/-- The ordered-field leg as a distinct instance of the single saturation engine, via the
same Fourier-Motzkin variable-elimination round as the integer leg (`Core.Eliminate`) but
with the *pure* rational `eliminateVar` (no integrality tightening). -/
instance instSaturation : Saturation (ElimState DFact) Cert where
  refuted? := elimRefuted? refuted?
  measure := elimMeasure
  round := elimRound eliminateVar

/-- Tag hypotheses with unit provenance.  Crucially, strict facts are passed through as
genuine `lt` (no `a < b ↦ a + 1 ≤ b` tightening): that is the sole data-level difference
from the integer leg and is what keeps rational-satisfiable strict systems unrefuted. -/
def ofHyps (hyps : List Fact) : Array DFact :=
  (Integer.ofHyps hyps).map DFact.ofInt

/-- Decide a linear ordered-field system: `Except.ok` with a Farkas certificate iff a
refutation was found.  Seeds the engine with the tagged hypotheses and elimination
schedule. -/
def solve (hyps : List Fact) : Except EngineError Cert :=
  let facts := ofHyps hyps
  let s : ElimState DFact := { facts := facts, todo := allVars facts }
  run #[s]

end OrderedField
end KanSaturation
