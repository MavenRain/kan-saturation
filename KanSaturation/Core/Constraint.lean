/-!
# `KanSaturation.Core.Constraint`

Mathlib-free constraint datatypes over core integer coefficients, shared by the
integer (`Instances.Integer`) and ordered-field (`Instances.OrderedField`) legs.
The ideal leg (`Instances.Ideal`) supplies its own polynomial fact type; this
module is the linear substrate.

Everything here is total or `Option`-returning (no exceptions, per the library
conventions), and depends only on core `Int`.
-/

namespace KanSaturation

/-- A variable, identified by an index. -/
abbrev Var := Nat

/-- A linear form `∑ cᵢ · xᵢ + c₀` over integer coefficients, stored sparsely as a
list of `(coefficient, variable)` terms plus a constant.  Like terms are merged by
`normalize`; intermediate forms may carry duplicate or zero terms. -/
structure LinForm where
  /-- Sparse `(coefficient, variable)` terms. -/
  terms : List (Int × Var)
  /-- The constant term. -/
  const : Int
  deriving Repr, BEq, Inhabited

namespace LinForm

/-- The zero form. -/
def zero : LinForm := { terms := [], const := 0 }

/-- Scale a form by an integer. -/
def scale (k : Int) (f : LinForm) : LinForm :=
  { terms := f.terms.map (fun (c, v) => (k * c, v)), const := k * f.const }

/-- Add two forms (without merging like terms; `normalize` merges and prunes). -/
def add (f g : LinForm) : LinForm :=
  { terms := f.terms ++ g.terms, const := f.const + g.const }

/-- The coefficient of variable `v` in `f` (summing any duplicate terms). -/
def coeffOf (f : LinForm) (v : Var) : Int :=
  f.terms.foldl (init := 0) fun acc (c, w) => if w == v then acc + c else acc

/-- The sorted set of variables occurring in `f`. -/
def vars (f : LinForm) : List Var :=
  (f.terms.map Prod.snd).eraseDups

/-- Merge like terms and drop zero coefficients, giving a canonical representation. -/
def normalize (f : LinForm) : LinForm :=
  let collected := f.vars.filterMap fun v =>
    let c := f.coeffOf v
    if c == 0 then none else some (c, v)
  { terms := collected, const := f.const }

/-- A canonical key for comparing forms *up to positive scaling and term order*:
normalize, divide out the content gcd (gcd of all coefficients and the constant), and
sort terms by variable.  Used only for deduplication in the saturation loop — the stored
form, hence any certificate combination, is never divided, so this does not affect the
replayed proof. -/
def key (f : LinForm) : LinForm :=
  let n := f.normalize
  let g : Nat := n.terms.foldl (init := n.const.natAbs) fun acc (c, _) => Nat.gcd acc c.natAbs
  let d : LinForm := if g > 1 then
      { terms := n.terms.map (fun (c, v) => (c / (g : Int), v)), const := n.const / (g : Int) }
    else n
  { d with terms := (d.terms.toArray.qsort (fun a b => decide (a.2 < b.2))).toList }

end LinForm

/-- The comparison a fact asserts of its form against `0`. -/
inductive Rel where
  /-- `form = 0`. -/
  | eq
  /-- `0 ≤ form`. -/
  | le
  /-- `0 < form`. -/
  | lt
  deriving Repr, BEq, Inhabited, DecidableEq

/-- A normalized constraint: the assertion `form `rel` 0`. -/
structure Fact where
  /-- Which relation is asserted. -/
  rel  : Rel
  /-- The linear form. -/
  form : LinForm
  deriving Repr, BEq, Inhabited

end KanSaturation
