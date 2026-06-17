import KanSaturation.Core.Constraint
import KanSaturation.Core.Saturation
import KanSaturation.Core.Engine

/-!
# `KanSaturation.Instances.Integer`

The integer leg: `omega` recovered as a `Saturation` instance.  The saturation step
is Fourier-Motzkin variable elimination (with equalities handled by sign-flipping),
carrying a nonnegative-combination *provenance* so a refutation is a replayable
Farkas-style certificate.

Soundness: every derived fact is a nonnegative-integer combination of the inputs, so
a derived constant-false fact (`0 ≤ -1`, `0 = 5`, `0 < 0`) refutes the system, and its
`combo` is exactly the certificate the tactic layer replays into a proof.

Scope (this phase): a sound core over linear-integer constraints.  Integer-specific
*tightening* (the Omega test's dark/grey shadows and `bmod` equality elimination) that
closes the rational/integer gap is deferred to production hardening (plan phase 6);
the present step is rational Fourier-Motzkin plus equality elimination, which is sound
for ℤ and complete for the rational-infeasible class.
-/

namespace KanSaturation
namespace Integer

/-- A derived fact: a constraint together with the nonnegative-integer combination of
the original hypotheses (keyed by hypothesis index) that produced it. -/
structure DFact where
  /-- The constraint `form rel 0`. -/
  fact  : Fact
  /-- Provenance: `∑ cᵢ · hypᵢ`, as `(coefficient, hypothesis-index)` pairs. -/
  combo : List (Int × Nat)
  deriving Repr, Inhabited

/-- Logical equality of derived facts compares only the constraint, *up to positive
scaling and term order* (via `LinForm.key`): the provenance is bookkeeping, and scalar
multiples of a constraint are logically equivalent, so the engine deduplicates them.
This is what lets the saturation loop reach a fixpoint instead of chasing `-3b, -6b, …`. -/
instance : BEq DFact where
  beq a b := a.fact.rel == b.fact.rel && a.fact.form.key == b.fact.form.key

/-- A refutation certificate: the combination of original hypotheses yielding a
manifestly false constant constraint, plus that residual for replay/diagnostics. -/
structure Cert where
  /-- `∑ cᵢ · hypᵢ` reducing to the residual. -/
  combo : List (Int × Nat)
  /-- The false residual, e.g. `0 ≤ -1`. -/
  residual : Fact
  deriving Repr, Inhabited

/-- Combine relations under nonnegative multipliers: `eq` is neutral, `lt` dominates.
Fully enumerated (no wildcard) per repo convention. -/
def combineRel : Rel → Rel → Rel
  | .eq, .eq => .eq
  | .eq, .le => .le
  | .eq, .lt => .lt
  | .le, .eq => .le
  | .le, .le => .le
  | .le, .lt => .lt
  | .lt, .eq => .lt
  | .lt, .le => .lt
  | .lt, .lt => .lt

/-- Negate a derived fact (flip the form and the provenance).  Sound only for `eq`
facts, where it is used to orient a same-sign elimination. -/
def negateD (d : DFact) : DFact :=
  { fact  := { d.fact with form := d.fact.form.scale (-1) }
    combo := d.combo.map (fun (c, i) => (-c, i)) }

/-- `md · d + me · e` at the fact and provenance level. -/
def combineWith (md : Int) (d : DFact) (me : Int) (e : DFact) : DFact :=
  { fact  := { rel  := combineRel d.fact.rel e.fact.rel
               form := (d.fact.form.scale md).add (e.fact.form.scale me) }
    combo := d.combo.map (fun (c, i) => (md * c, i))
               ++ e.combo.map (fun (c, i) => (me * c, i)) }

/-- Eliminate variable `v` between `d` and `e` with nonnegative multipliers, when
soundly possible: opposite-sign coefficients combine directly; a same-sign pair
combines only by flipping an `eq` side. -/
def resolve (v : Var) (d e : DFact) : Option DFact :=
  let a := d.fact.form.coeffOf v
  let b := e.fact.form.coeffOf v
  if a == 0 || b == 0 then
    none
  else if a * b < 0 then
    some (combineWith (Int.ofNat b.natAbs) d (Int.ofNat a.natAbs) e)
  else
    match d.fact.rel, e.fact.rel with
    | .eq, .eq => some (combineWith (Int.ofNat b.natAbs) (negateD d) (Int.ofNat a.natAbs) e)
    | .eq, .le => some (combineWith (Int.ofNat b.natAbs) (negateD d) (Int.ofNat a.natAbs) e)
    | .eq, .lt => some (combineWith (Int.ofNat b.natAbs) (negateD d) (Int.ofNat a.natAbs) e)
    | .le, .eq => some (combineWith (Int.ofNat b.natAbs) d (Int.ofNat a.natAbs) (negateD e))
    | .lt, .eq => some (combineWith (Int.ofNat b.natAbs) d (Int.ofNat a.natAbs) (negateD e))
    | .le, .le => none
    | .le, .lt => none
    | .lt, .le => none
    | .lt, .lt => none

/-- A magnitude cap on derived coefficients.  Resolvents whose coefficients or constant
exceed it are dropped — a *sound* incompleteness bound (dropping a derived fact can only
cost a refutation, never fabricate one), which stops the accumulate-only saturation loop
from chasing the unbounded coefficient growth of cyclic systems with non-unit
coefficients.  Realistic Farkas certificates have tiny coefficients, far under this. -/
def coeffCap : Nat := 1 <<< 14

/-- Whether any coefficient or the constant of `f` exceeds `coeffCap` in magnitude. -/
def tooBig (f : LinForm) : Bool :=
  f.const.natAbs > coeffCap || f.terms.any fun ce => ce.1.natAbs > coeffCap

/-- The saturation step: all sound one-variable eliminations of `d` against `basis`,
dropping any resolvent whose coefficients exceed `coeffCap`. -/
def consequences (basis : Array DFact) (d : DFact) : Array DFact :=
  d.fact.form.vars.foldl (init := #[]) fun acc v =>
    basis.foldl (init := acc) fun acc' e =>
      (resolve v d e).elim acc' fun r =>
        if tooBig r.fact.form then acc' else acc'.push r

/-- Detect a derived constant-false fact and return its certificate. -/
def refuted? (basis : Array DFact) : Option Cert :=
  basis.findSome? fun d =>
    let f := d.fact.form.normalize
    if f.terms.isEmpty then
      let isFalse : Bool :=
        match d.fact.rel with
        | .eq => f.const != 0
        | .le => decide (f.const < 0)
        | .lt => decide (f.const ≤ 0)
      if isFalse then
        some { combo := d.combo, residual := { rel := d.fact.rel, form := f } }
      else
        none
    else
      none

/-- The integer leg as an instance of the single saturation engine. -/
instance instSaturation : Saturation DFact Cert where
  consequences := consequences
  measure d := d.fact.form.terms.length
  reduce _ d := { d with fact := { d.fact with form := d.fact.form.normalize } }
  refuted? := refuted?

/-- Tag a list of hypotheses with unit provenance (`hypᵢ` with coefficient `1`). -/
def ofHyps (hyps : List Fact) : Array DFact :=
  (List.range hyps.length).foldl (init := #[]) fun acc i =>
    match hyps[i]? with
    | some f => acc.push { fact := f, combo := [((1 : Int), i)] }
    | none   => acc

/-- Decide a linear-integer system: `Except.ok` with a certificate iff a refutation
was found within the fuel bound.  (Named `solve` to avoid shadowing the core
`Decidable.decide` used above.) -/
def solve (hyps : List Fact) (fuel : Nat := 1000) : Except EngineError Cert :=
  run (ofHyps hyps) fuel

end Integer
end KanSaturation
