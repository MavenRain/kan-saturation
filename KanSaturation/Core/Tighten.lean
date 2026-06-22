import KanSaturation.Core.Constraint
import KanSaturation.Core.Eval
import KanTactics

/-!
# `KanSaturation.Core.Tighten`

**Integer tightening**: the soundness substrate that closes the ℤ/ℚ gap.  Over `ℤ`, a
`≤`-constraint `0 ≤ ∑ aᵢxᵢ + c` whose variable coefficients share a common divisor `g > 0`
can be *tightened*: `∑ aᵢxᵢ` is then a multiple of `g`, so `∑ aᵢxᵢ ≥ -c` sharpens to
`∑ aᵢxᵢ ≥ g·⌈-c/g⌉ = -g·⌊c/g⌋`, i.e. the constant `c` may be replaced by the smaller
`g·⌊c/g⌋`.  This is the integer-rounding step `omega` performs (the GCD test on a single
constraint); applied to a system it refutes integer-infeasible-but-rational-feasible cases
such as `2x = 1` (where the two `≤` directions tighten to `x ≤ 0` and `x ≥ 1`).

Soundness rests on this module's kan-tactics-only lemmas and is replayed per call by the
tactic layer (the tightened fact is added to the engine's pool as an extra *sound*
hypothesis, so the existing Farkas replay folds it with no change to the certificate shape).
Floor division is core `Int` Euclidean division (`/` on `Int`), which equals `⌊·/g⌋` for
`g > 0`.

Scope: this is the single-constraint GCD tightening (sound, branch-free).  The full Omega
test's dark/grey-shadow splinter case-splits (which need a *branching* search) and `bmod`
equality elimination remain the documented completeness frontier.
-/

namespace KanSaturation

/-- The GCD-tightened form: same linear terms, constant replaced by `g · ⌊c/g⌋`.  Sound to
assert (over `ℤ`) exactly when `g` divides every variable coefficient and `g > 0`; both are
checked by the caller and discharged in `holds_gcdTighten`. -/
def LinForm.gcdTighten (g : Int) (f : LinForm) : LinForm :=
  { f with const := g * (f.const / g) }

/-- Whether `g` divides a term's coefficient (the per-term tightening guard). -/
def dvdCoeff (g : Int) (t : Int × Var) : Bool := decide (g ∣ t.1)

/-- If `g` divides every coefficient of a term list, it divides the list's evaluation. -/
theorem dvd_sumTerms (env : Var → Int) (g : Int) (terms : List (Int × Var)) :
    terms.all (dvdCoeff g) = true → g ∣ sumTerms env terms := by
  kan_refine (List.rec (motive := fun L =>
    L.all (dvdCoeff g) = true → g ∣ sumTerms env L) ?nil ?cons terms)
  · kan_intro h0
    kan_exact (Int.dvd_zero g)
  · kan_intro head
    kan_intro tail
    kan_intro ih
    kan_intro hcons
    kan_exact (Int.dvd_add
      (Int.dvd_mul_of_dvd_left (of_decide_eq_true (Bool.and_eq_true_iff.mp hcons).1))
      (ih (Bool.and_eq_true_iff.mp hcons).2))

/-- The core floor-tightening step: for `g > 0`, `0 ≤ g·k + c ⟹ 0 ≤ k + ⌊c/g⌋`. -/
theorem le_add_ediv_of_le (g k c : Int) (hg : 0 < g) (h : 0 ≤ g * k + c) :
    0 ≤ k + c / g :=
  Int.add_nonneg_iff_neg_le'.mpr
    ((Int.le_ediv_iff_mul_le hg).mpr
      (Int.neg_mul k g ▸ Int.add_nonneg_iff_neg_le'.mp (Int.mul_comm g k ▸ h)))

/-- Tightening the constant of a `g`-divisible total: `0 ≤ M + c ⟹ 0 ≤ M + g·⌊c/g⌋`. -/
theorem le_add_mul_ediv_of_dvd (g M c : Int) (hg : 0 < g) (hd : g ∣ M) (h : 0 ≤ M + c) :
    0 ≤ M + g * (c / g) :=
  hd.elim fun k hk =>
    hk ▸ ((Int.mul_add g k (c / g)).symm ▸
      Int.mul_nonneg (Int.le_of_lt hg) (le_add_ediv_of_le g k c hg (hk ▸ h)))

/-- **Tightening soundness.**  When `g > 0` divides every variable coefficient of `f`, the
GCD-tightened form holds wherever `f` does (over an integer environment). -/
theorem holds_gcdTighten (env : Var → Int) (g : Int) (f : LinForm) (hg : 0 < g)
    (hdvd : f.terms.all (dvdCoeff g) = true) (h : 0 ≤ f.eval env) :
    0 ≤ (f.gcdTighten g).eval env :=
  le_add_mul_ediv_of_dvd g (sumTerms env f.terms) f.const hg (dvd_sumTerms env g f.terms hdvd) h

end KanSaturation
