import KanSaturation.Core.Constraint
import KanSaturation.Core.Saturation
import KanSaturation.Core.Engine
import KanSaturation.Core.Eliminate

/-!
# `KanSaturation.Instances.Integer`

The integer leg: `omega` recovered as a `Saturation` instance.  The saturation step
is Fourier-Motzkin variable elimination (with equalities handled by sign-flipping),
carrying a nonnegative-combination *provenance* so a refutation is a replayable
Farkas-style certificate.

Soundness: every derived fact is a nonnegative-integer combination of the inputs, so
a derived constant-false fact (`0 ≤ -1`, `0 = 5`, `0 < 0`) refutes the system, and its
`combo` is exactly the certificate the tactic layer replays into a proof.

The `round` is a genuine **variable-elimination** step (`Core.Eliminate`): one variable per
round, dropping every constraint that mentions it, so the engine terminates by the variable
count.  This refutes the full rational-infeasible class.  The ℤ/ℚ gap is closed by the *sound
integer tightening* of `Core.Tighten` (gcd rounding of a single constraint), replayed at the
tactic boundary; the Omega test's dark/grey-shadow splinters (a branching search) and `bmod`
equality elimination remain the documented completeness frontier.
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

/-- All variables occurring across a derived-fact array (deduplicated), in occurrence order:
the Fourier-Motzkin elimination schedule.  Every resolvent's variables are a subset of its
parents', so this set never grows, and eliminating each in turn drives the system to
constant constraints. -/
def allVars (facts : Array DFact) : List Var :=
  (facts.toList.flatMap (fun d => d.fact.form.vars)).eraseDups

/-- Deduplicate derived facts up to positive scaling and term order (via the `BEq` `key`),
keeping the first occurrence.  Completeness-preserving (scalar multiples are logically
equivalent), and keeps the eliminated basis from carrying redundant copies. -/
def dedup (facts : Array DFact) : Array DFact :=
  facts.foldl (init := #[]) fun acc d => if acc.contains d then acc else acc.push d

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

/-- Normal-form reduction of a derived fact (merge like terms, drop zero coefficients). -/
def reduceFact (d : DFact) : DFact :=
  { d with fact := { d.fact with form := d.fact.form.normalize } }

/-- Eliminate variable `v` by Fourier-Motzkin: keep the constraints free of `v`, add every
sound resolvent that cancels `v` between two constraints containing it (each unordered pair
once; `resolve` returns `none` for the pairs that cannot eliminate `v`, e.g. two same-sign
inequalities), drop the rest, then normalize and deduplicate.  Each resolvent is a
nonnegative-integer combination of its parents, so the `combo` provenance stays a Farkas
certificate; normalizing drops `v`'s now-zero coefficient so the result is `v`-free. -/
def eliminateVar (v : Var) (facts : Array DFact) : Array DFact :=
  let withoutV := facts.filter (fun d => d.fact.form.coeffOf v == 0)
  let withV    := facts.filter (fun d => d.fact.form.coeffOf v != 0)
  let n := withV.size
  let resolvents : Array DFact :=
    (List.range n).foldl (init := #[]) fun acc i =>
      (List.range n).foldl (init := acc) fun acc' j =>
        if i < j then
          (withV[i]?.bind fun d => withV[j]?.bind fun e => resolve v d e).elim acc'
            (fun r => acc'.push r)
        else acc'
  dedup ((withoutV ++ resolvents).map reduceFact)

/-- The integer leg as an instance of the single saturation engine, via the Fourier-Motzkin
variable-elimination round (`Core.Eliminate`): one variable per round, dropping every
constraint that mentions it, with the variable count as the well-founded measure. -/
instance instSaturation : Saturation (ElimState DFact) Cert where
  refuted? := elimRefuted? refuted?
  measure := elimMeasure
  round := elimRound eliminateVar

/-- Tag a list of hypotheses with unit provenance (`hypᵢ` with coefficient `1`). -/
def ofHyps (hyps : List Fact) : Array DFact :=
  (List.range hyps.length).foldl (init := #[]) fun acc i =>
    (hyps[i]?).elim acc (fun f => acc.push { fact := f, combo := [((1 : Int), i)] })

/-- Decide a linear-integer system: `Except.ok` with a certificate iff a refutation was
found.  Seeds the engine with the tagged hypotheses and the full elimination schedule.
(Named `solve` to avoid shadowing the core `Decidable.decide` used above.) -/
def solve (hyps : List Fact) : Except EngineError Cert :=
  let facts := ofHyps hyps
  let s : ElimState DFact := { facts := facts, todo := allVars facts }
  run #[s]

end Integer
end KanSaturation
