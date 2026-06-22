import KanSaturation.Core.Constraint
import KanSaturation.Core.Saturation
import KanSaturation.Core.Engine
import KanSaturation.Core.PolyReflect

/-!
# `KanSaturation.Instances.Ideal`

The ideal leg: `polyrith` recovered as a `Saturation` instance.  The saturation step is
**Buchberger superposition** (S-polynomials reduced to normal form modulo the current
basis) over a polynomial ideal with `ℚ` coefficients, carrying a **cofactor provenance**
so a refutation is a replayable ideal-membership (Nullstellensatz) certificate.

Soundness: every derived polynomial is a polynomial combination `∑ qᵢ · hypᵢ` of the
original generators (the `combo` records the cofactor `qᵢ` per generator index `i`), so a
derived **nonzero constant** polynomial `c` exhibits `c = ∑ qᵢ · hypᵢ` with each `hypᵢ = 0`,
forcing `c = 0`, a contradiction the tactic layer replays into a kernel-checked proof.
The single structural divergence from the integer / ordered-field `DFact` is that there is
**no `Rel`** here: ideal generators are pure equalities (`poly = 0`), which is exactly what
justifies a distinct `Saturation` instance (as `Instances.OrderedField` justifies its own).

Scope (this leg): a *sound* core over polynomial-equality systems.  Coefficients are core
`Rat` (field reduction divides by leading coefficients cleanly; `ℤ` would force
pseudo-division, which is not a Gröbner procedure).  The monomial order is **graded-lex**,
used only for leading-term selection and dedup; soundness is the kernel-checked eval
replay and is independent of the order.  The *tightness theorem* for this leg is
**Hilbert's Nullstellensatz** (an infeasible system has a `1 ∈ ⟨hyps⟩` certificate); as in
the other legs it is documented, **not** load-bearing for soundness, which rests on the
per-call kernel-checked replay.  This leg uses the engine's **bounded accumulate** round
(`Core.Engine.accumulateRound`): Buchberger never drops a fact, so it has no variable-count
measure and is instead bounded by the capacity measure `cap + 1 - basis.size` (a refused fact
can only cost a refutation, never fabricate one); a genuine Buchberger completeness story is
deferred.
-/

namespace KanSaturation
namespace Ideal

/-! ## Monomial arithmetic (on the exponent vector `Mono.vars`) -/

/-- Total exponent of variable `v` across a (possibly unsorted/duplicated) exponent vector. -/
def expOf (vs : List (Var × Nat)) (v : Var) : Nat :=
  vs.foldl (init := 0) fun acc t => if t.1 == v then acc + t.2 else acc

/-- The variables occurring in an exponent vector (deduplicated). -/
def monoVarsOf (vs : List (Var × Nat)) : List Var := (vs.map Prod.fst).eraseDups

/-- Canonical exponent vector: merge duplicate variables (summing exponents), drop zero
exponents, and sort ascending by variable index. -/
def monoNorm (vs : List (Var × Nat)) : List (Var × Nat) :=
  let collected := (monoVarsOf vs).filterMap fun v =>
    let e := expOf vs v
    if e == 0 then none else some (v, e)
  (collected.toArray.qsort (fun a b => decide (a.1 < b.1))).toList

/-- Total degree of a monomial (sum of exponents; order-independent, so computed raw). -/
def monoDegree (vs : List (Var × Nat)) : Nat := vs.foldl (init := 0) fun acc t => acc + t.2

/-- Lexicographic comparison of two *canonical* (sorted-ascending) exponent vectors. -/
def lexVars : List (Var × Nat) → List (Var × Nat) → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | (v1, e1) :: r1, (v2, e2) :: r2 =>
      if v1 == v2 then (if e1 == e2 then lexVars r1 r2 else compare e1 e2)
      else compare v1 v2

/-- Graded-lex monomial order: by total degree, then lex on the canonical exponent vector.
A total order whose only ties are genuinely-equal monomials, so `normPoly` is canonical. -/
def monoCmp (a b : List (Var × Nat)) : Ordering :=
  let a' := monoNorm a
  let b' := monoNorm b
  match compare (monoDegree a') (monoDegree b') with
  | .eq => lexVars a' b'
  | .lt => .lt
  | .gt => .gt

/-- Least common multiple of two monomials (max exponent per variable). -/
def monoLcm (a b : List (Var × Nat)) : List (Var × Nat) :=
  let a' := monoNorm a
  let b' := monoNorm b
  let vars := ((a'.map Prod.fst) ++ (b'.map Prod.fst)).eraseDups
  vars.filterMap fun v =>
    let e := Nat.max (expOf a' v) (expOf b' v)
    if e == 0 then none else some (v, e)

/-- Monomial division `a / b`: the per-variable exponent difference, or `none` when `b`
does not divide `a` (some variable's exponent in `b` exceeds that in `a`). -/
def monoDiv? (a b : List (Var × Nat)) : Option (List (Var × Nat)) :=
  let a' := monoNorm a
  let b' := monoNorm b
  let vars := ((a'.map Prod.fst) ++ (b'.map Prod.fst)).eraseDups
  vars.foldl (init := some []) fun acc v =>
    acc.bind fun resVars =>
      let ea := expOf a' v
      let eb := expOf b' v
      if eb > ea then none
      else
        let e := ea - eb
        if e == 0 then some resVars else some (resVars ++ [(v, e)])

/-! ## Polynomial canonicalization, leading term, refutation residue -/

/-- Canonical form of a polynomial: normalize each monomial's exponent vector, merge like
monomials (summing coefficients, via `collapseP`), drop zero coefficients, and sort terms
**descending** by `monoCmp` so the leading term is first.  A true canonical form (equal
polynomials share a normal form), so it backs both dedup and refutation detection. -/
def normPoly (p : MvPoly) : MvPoly :=
  let normed := p.terms.map (fun m => (⟨m.coeff, monoNorm m.vars⟩ : Mono))
  let merged := collapseP normed
  let nonzero := merged.filter (fun m => !(m.coeff == 0))
  ⟨(nonzero.toArray.qsort (fun a b => monoCmp a.vars b.vars == Ordering.gt)).toList⟩

/-- The leading (largest) monomial term, or `none` for the zero polynomial. -/
def leadTerm? (p : MvPoly) : Option Mono := (normPoly p).terms.head?

/-- Whether a polynomial is zero (empty canonical form). -/
def isZeroPoly (p : MvPoly) : Bool := (normPoly p).terms.isEmpty

/-- A canonical key for dedup *up to nonzero scaling*: the canonical form made monic by
dividing through the leading coefficient.  **Dedup only**: the stored polynomial and its
cofactor combo are never monic-divided (cf. `LinForm.key` in `Core.Constraint`), so the
replayed certificate is exact. -/
def polyKey (p : MvPoly) : MvPoly :=
  let n := normPoly p
  n.terms.head?.elim n (fun lead =>
    if lead.coeff == 0 then n
    else ⟨n.terms.map (fun m => ⟨m.coeff / lead.coeff, m.vars⟩)⟩)

/-! ## Derived facts and certificate, with cofactor provenance -/

/-- A derived fact: a polynomial asserted equal to `0`, together with the cofactor
combination `∑ qᵢ · hypᵢ` (keyed by generator index) that produced it. -/
structure PFact where
  /-- The polynomial `poly = 0`. -/
  poly : MvPoly
  /-- Provenance: `∑ qᵢ · hypᵢ`, as `(cofactor-polynomial, generator-index)` pairs. -/
  combo : List (MvPoly × Nat)
  deriving Repr, Inhabited

/-- Logical equality of derived facts compares only the polynomial, *up to nonzero scaling
and monomial order* (via `polyKey`): provenance is bookkeeping and scalar multiples are
logically equivalent, so the saturation loop deduplicates them and can reach a fixpoint
(mirrors `Integer.DFact`'s `BEq`). -/
instance : BEq PFact where
  beq a b := polyKey a.poly == polyKey b.poly

/-- A refutation certificate: the cofactor combination yielding a manifestly nonzero
constant polynomial, plus that constant for diagnostics.  `residual ≠ 0` witnesses
"a nonzero constant lies in the ideal" (the replay reconstructs `residual = ∑ qᵢ · hypᵢ`
and contradicts `residual ≠ 0` against each `hypᵢ = 0`). -/
structure Cert where
  /-- `∑ qᵢ · hypᵢ` reducing to the nonzero constant residue. -/
  combo : List (MvPoly × Nat)
  /-- The nonzero constant residue. -/
  residual : Rat
  deriving Repr, Inhabited

/-! ## Cofactor combinators (the sole provenance-threading site)

Each mirrors a polynomial operation so the invariant `poly ≈ ∑ combo` is preserved (up to
canonical form): scaling the polynomial by a monomial scales every cofactor by it;
negating the polynomial negates every cofactor; combining concatenates. -/

/-- Scale every cofactor by a monomial (mirrors `MvPoly.scaleMono` on the polynomial). -/
def comboScaleMono (m : Mono) (combo : List (MvPoly × Nat)) : List (MvPoly × Nat) :=
  combo.map (fun t => (t.1.scaleMono m, t.2))

/-- Negate every cofactor (mirrors `MvPoly.neg`). -/
def comboNeg (combo : List (MvPoly × Nat)) : List (MvPoly × Nat) :=
  combo.map (fun t => (t.1.neg, t.2))

/-- Combine two cofactor lists (mirrors `MvPoly.add`). -/
def comboConcat (c1 c2 : List (MvPoly × Nat)) : List (MvPoly × Nat) := c1 ++ c2

/-! ## The Buchberger saturation step -/

/-- The S-polynomial of two derived facts (with cofactor provenance), cancelling their
leading terms over `ℚ`: `S = (1/lc d)·(L/lm d)·d − (1/lc e)·(L/lm e)·e` where `L` is the
leading-monomial lcm.  `none` when either is zero. -/
def sPoly (d e : PFact) : Option PFact :=
  (leadTerm? d.poly).bind fun ld =>
    (leadTerm? e.poly).bind fun le =>
      if ld.coeff == 0 || le.coeff == 0 then none
      else
        let lm := monoLcm ld.vars le.vars
        (monoDiv? lm ld.vars).bind fun mdVars =>
          (monoDiv? lm le.vars).bind fun meVars =>
            let md : Mono := ⟨1 / ld.coeff, mdVars⟩
            let me : Mono := ⟨1 / le.coeff, meVars⟩
            let poly := (d.poly.scaleMono md).sub (e.poly.scaleMono me)
            let combo := comboConcat (comboScaleMono md d.combo)
              (comboNeg (comboScaleMono me e.combo))
            some ⟨poly, combo⟩

/-- One top-reduction step: if some basis element's leading monomial divides `d`'s leading
monomial, subtract the scaled multiple that cancels `d`'s leading term (threading
cofactors).  `none` when `d`'s leading term is reducible by no basis element. -/
def reduceStep? (basis : Array PFact) (d : PFact) : Option PFact :=
  (leadTerm? d.poly).bind fun ld =>
    if ld.coeff == 0 then none
    else
      basis.findSome? fun b =>
        (leadTerm? b.poly).bind fun lb =>
          if lb.coeff == 0 then none
          else (monoDiv? ld.vars lb.vars).map fun qVars =>
            let m : Mono := ⟨ld.coeff / lb.coeff, qVars⟩
            let poly := d.poly.sub (b.poly.scaleMono m)
            let combo := comboConcat d.combo (comboNeg (comboScaleMono m b.combo))
            (⟨poly, combo⟩ : PFact)

/-- Normal form of `d` modulo `basis` by repeated top-reduction, bounded by `fuel`
(a `def`, not `partial`; over-reduction only costs completeness). -/
def normForm : Nat → Array PFact → PFact → PFact
  | 0, _, d => d
  | fuel + 1, basis, d => (reduceStep? basis d).elim d (fun d' => normForm fuel basis d')

/-- Fuel for a single normal-form reduction. -/
def reduceFuel : Nat := 64

/-- A degree cap on derived polynomials: resolvents whose total degree exceeds it are
dropped, a *sound* incompleteness bound (a dropped fact can only cost a refutation, never
fabricate one) that bounds the accumulate-only saturation loop. -/
def degreeCap : Nat := 64

/-- Whether any monomial of `p` exceeds the degree cap. -/
def tooBig (p : MvPoly) : Bool := (normPoly p).terms.any fun m => decide (monoDegree m.vars > degreeCap)

/-- The saturation step: all S-polynomials of `d` against the basis, each reduced to normal
form modulo the basis, dropping zero and over-degree resolvents. -/
def consequences (basis : Array PFact) (d : PFact) : Array PFact :=
  ((basis.filterMap (fun e => sPoly d e)).map (fun s => normForm reduceFuel basis s)).filter
    (fun s => !isZeroPoly s.poly && !tooBig s.poly)

/-- Detect a derived nonzero-constant fact (`1 ∈ ⟨hyps⟩` witness) and return its certificate. -/
def refuted? (basis : Array PFact) : Option Cert :=
  basis.findSome? fun d =>
    let ts := (normPoly d.poly).terms
    ts.head?.bind fun m =>
      if ts.length == 1 && m.vars.isEmpty && !(m.coeff == 0) then
        some ⟨d.combo, m.coeff⟩
      else none

/-- Normal-form reduction of a derived fact (canonical polynomial). -/
def reduceFact (d : PFact) : PFact := ⟨normPoly d.poly, d.combo⟩

/-- The accumulate superposition step: the Buchberger S-polynomial consequences of every
basis fact, each reduced to normal form modulo the basis. -/
def step (basis : Array PFact) : Array PFact :=
  basis.foldl (init := #[]) fun acc f => acc ++ (consequences basis f).map reduceFact

/-- The ideal leg as an instance of the single saturation engine, via the bounded
accumulate round over Buchberger superposition. -/
instance instSaturation : Saturation PFact Cert where
  refuted? := refuted?
  measure := capMeasure
  round := accumulateRound step

/-- Tag a list of generator polynomials with unit cofactor provenance (`hypᵢ` with
cofactor `1` at index `i`). -/
def ofHyps (hyps : List MvPoly) : Array PFact :=
  (List.range hyps.length).foldl (init := #[]) fun acc i =>
    (hyps[i]?).elim acc (fun p => acc.push ⟨p, [(MvPoly.one, i)]⟩)

/-- Decide a polynomial-equality system: `Except.ok` with a Nullstellensatz cofactor
certificate iff a nonzero constant was derived in the ideal. -/
def solve (hyps : List MvPoly) : Except EngineError Cert :=
  run (ofHyps hyps)

/-! ## Ideal membership (for equality goals)

Proving an equality goal `a = b` is proving `a − b ∈ ⟨hyps⟩` (the `polyrith` direction):
reduce the goal polynomial to normal form modulo the generators and, if it reaches `0`,
read off the cofactor representation `goal = ∑ qᵢ · hypᵢ`.  The tracked invariant here is
`goal = poly + ∑ combo` (note: **no** sign flip, unlike `reduceStep?`'s `poly = ∑ combo`),
so when `poly` reaches `0` the accumulated `combo` *is* the membership certificate.

First cut: reduction is modulo the *raw* generators (not the saturated Gröbner basis), so
membership is complete only where the generators already reduce the goal, exactly the
documented restricted class.  Saturating before reducing is deferred. -/

/-- One membership-reduction step under the invariant `goal = poly + ∑ combo`. -/
def memberStep? (basis : Array PFact) (d : PFact) : Option PFact :=
  (leadTerm? d.poly).bind fun ld =>
    if ld.coeff == 0 then none
    else
      basis.findSome? fun b =>
        (leadTerm? b.poly).bind fun lb =>
          if lb.coeff == 0 then none
          else (monoDiv? ld.vars lb.vars).map fun qVars =>
            let m : Mono := ⟨ld.coeff / lb.coeff, qVars⟩
            let poly := d.poly.sub (b.poly.scaleMono m)
            let combo := comboConcat d.combo (comboScaleMono m b.combo)
            (⟨poly, combo⟩ : PFact)

/-- Normal form of `d` modulo `basis` for membership (fuel-bounded). -/
def memberForm : Nat → Array PFact → PFact → PFact
  | 0, _, d => d
  | fuel + 1, basis, d => (memberStep? basis d).elim d (fun d' => memberForm fuel basis d')

/-- If `goal` reduces to `0` modulo the generators, return the cofactor representation
`goal = ∑ qᵢ · hypᵢ`; otherwise `none`. -/
def member? (hyps : List MvPoly) (goal : MvPoly) (fuel : Nat := 1000) :
    Option (List (MvPoly × Nat)) :=
  let reduced := memberForm fuel (ofHyps hyps) ⟨goal, []⟩
  if isZeroPoly reduced.poly then some reduced.combo else none

/-! ## Certificate audit (data-level self-check)

`auditCombo` recomputes `∑ qᵢ · hypᵢ` from a cofactor list and the original generators.
A correct certificate's `combo` recomputes to its `residual` constant (checked in the demo
target), validating the cofactor threading end-to-end without any tactic machinery. -/

/-- Recompute `∑ qᵢ · hypᵢ` (canonicalized) from a cofactor combo over the generators. -/
def auditCombo (hyps : List MvPoly) (combo : List (MvPoly × Nat)) : MvPoly :=
  normPoly (combo.foldl (init := MvPoly.zero) fun acc t =>
    (hyps[t.2]?).elim acc (fun h => acc.add (t.1.mul h)))

end Ideal
end KanSaturation
