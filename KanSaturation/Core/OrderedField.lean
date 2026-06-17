import KanSaturation.Core.Constraint
import KanSaturation.Core.Collapse
import KanTactics

/-!
# `KanSaturation.Core.OrderedField`

The **ordered-field substrate**: the carrier over which the `linarith` leg
(`Instances.OrderedField`) is sound.  Where the integer leg evaluates forms over
`ℤ` (`Core.Eval`/`Core.Reflect`), `linarith` is sound over *any* ordered field, so
this module abstracts the carrier into a Mathlib-free `OrderedField` typeclass and
reproves the certificate-replay soundness lemmas generically over it.  The concrete
flagship instance (`ℚ`, core `Rat`) lives in `Instances.OrderedField`.

The class is deliberately hand-rolled (the library convention: own foundations, no
Mathlib, no coupling to `grind`'s internal algebra classes).  Its fields are exactly
the ordered-field facts the Farkas replay needs; every one is a core `Rat.*` lemma,
so the `ℚ` instance is immediate.

Per the project convention all proofs here are **kan-tactics only** (no
`simp`/`ring`/`linarith`): this is the irreducible ordered-field bootstrap, the
field analogue of `Core.Eval`.  Proofs mirror the integer substrate, applying the
recursor explicitly (`kan_refine (List.rec (motive := …) …)`) since `kan_induction`
cannot infer the motive, and closing with `kan_exact` of explicit terms.

The one genuine novelty over the integer leg is the **strict** path: `linarith`
keeps `<` strict (it does *not* tighten `a < b` to `a + 1 ≤ b`, which would be unsound
over a field), so the soundness layer carries strict-combination lemmas
(`holdsK_lt_*`) and a strict refutation closer (`falseK_of_fold_lt`) absent from the
integer leg.
-/

namespace KanSaturation

/-- A Mathlib-free **ordered field**: a commutative field with a linear order
compatible with the operations, plus the order-preserving integer cast the form
coefficients are interpreted through.  Bundled as exactly the data the Farkas
certificate replay consumes; `ℚ` is the flagship instance (`Instances.OrderedField`).

Stated over `Type` (the carriers of interest — `ℚ`, `ℝ` — are `Type 0`).  Field
inverse is included so the class is honestly an ordered *field*; the soundness layer
itself only uses the ordered-commutative-ring fragment. -/
class OrderedField (K : Type) extends
    Zero K, One K, Add K, Mul K, Neg K, Sub K, Inv K, Div K, IntCast K, LE K, LT K where
  /-- Addition is commutative. -/
  add_comm : ∀ a b : K, a + b = b + a
  /-- Addition is associative. -/
  add_assoc : ∀ a b c : K, a + b + c = a + (b + c)
  /-- `0` is a left identity for `+`. -/
  zero_add : ∀ a : K, 0 + a = a
  /-- `0` is a right identity for `+`. -/
  add_zero : ∀ a : K, a + 0 = a
  /-- `-a` is a left inverse for `+`. -/
  neg_add_cancel : ∀ a : K, -a + a = 0
  /-- Multiplication is associative. -/
  mul_assoc : ∀ a b c : K, a * b * c = a * (b * c)
  /-- Multiplication is commutative. -/
  mul_comm : ∀ a b : K, a * b = b * a
  /-- `1` is a left identity for `*`. -/
  one_mul : ∀ a : K, 1 * a = a
  /-- `a * 0 = 0`. -/
  mul_zero : ∀ a : K, a * 0 = 0
  /-- Left distributivity. -/
  mul_add : ∀ a b c : K, a * (b + c) = a * b + a * c
  /-- Subtraction is addition of the negation. -/
  sub_eq_add_neg : ∀ a b : K, a - b = a + -b
  /-- Every nonzero element has a multiplicative inverse (the field axiom). -/
  mul_inv_cancel : ∀ a : K, a ≠ 0 → a * a⁻¹ = 1
  /-- Dividing then multiplying by a nonzero cancels (for denominator clearing). -/
  div_mul_cancel : ∀ a b : K, b ≠ 0 → a / b * b = a
  /-- `((0 : ℤ) : K) = 0`. -/
  intCast_zero : ((0 : Int) : K) = 0
  /-- `((1 : ℤ) : K) = 1`. -/
  intCast_one : ((1 : Int) : K) = 1
  /-- The integer cast is additive. -/
  intCast_add : ∀ a b : Int, ((a + b : Int) : K) = (a : K) + (b : K)
  /-- The integer cast is multiplicative. -/
  intCast_mul : ∀ a b : Int, ((a * b : Int) : K) = (a : K) * (b : K)
  /-- The integer cast respects negation. -/
  intCast_neg : ∀ a : Int, ((-a : Int) : K) = -((a : K))
  /-- `≤` is reflexive. -/
  le_refl : ∀ a : K, a ≤ a
  /-- `≤` is transitive. -/
  le_trans : ∀ a b c : K, a ≤ b → b ≤ c → a ≤ c
  /-- `≤` is antisymmetric. -/
  le_antisymm : ∀ a b : K, a ≤ b → b ≤ a → a = b
  /-- `<` implies `≤`. -/
  le_of_lt : ∀ a b : K, a < b → a ≤ b
  /-- `<` is irreflexive. -/
  lt_irrefl : ∀ a : K, ¬ a < a
  /-- `<` is `≤`-and-`≠` (the order is linear, so this characterizes strictness). -/
  lt_iff_le_and_ne : ∀ a b : K, a < b ↔ a ≤ b ∧ a ≠ b
  /-- The order is linear: `¬ a ≤ b` is `b < a`. -/
  not_le : ∀ a b : K, ¬ a ≤ b ↔ b < a
  /-- Addition is monotone on the left. -/
  add_le_add_left : ∀ a b c : K, a ≤ b → c + a ≤ c + b
  /-- Addition is strictly monotone on the left. -/
  add_lt_add_left : ∀ a b c : K, a < b → c + a < c + b
  /-- A product of nonnegatives is nonnegative. -/
  mul_nonneg : ∀ a b : K, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
  /-- A product of positives is positive. -/
  mul_pos : ∀ a b : K, 0 < a → 0 < b → 0 < a * b
  /-- Left multiplication by a nonnegative is monotone (for denominator clearing). -/
  mul_le_mul_of_nonneg_left : ∀ a b c : K, a ≤ b → 0 ≤ c → c * a ≤ c * b
  /-- Left multiplication by a positive is strictly monotone (for denominator clearing). -/
  mul_lt_mul_of_pos_left : ∀ a b c : K, a < b → 0 < c → c * a < c * b
  /-- The integer cast preserves nonnegativity. -/
  intCast_nonneg : ∀ a : Int, 0 ≤ a → (0 : K) ≤ (a : K)
  /-- The integer cast preserves positivity. -/
  intCast_pos : ∀ a : Int, 0 < a → (0 : K) < (a : K)
  /-- The integer cast is monotone. -/
  intCast_le : ∀ a b : Int, a ≤ b → (a : K) ≤ (b : K)
  /-- The integer cast is strictly monotone. -/
  intCast_lt : ∀ a b : Int, a < b → (a : K) < (b : K)
  /-- The integer cast is injective. -/
  intCast_inj : ∀ a b : Int, (a : K) = (b : K) → a = b

namespace OrderedField

variable {K : Type} [OrderedField K]

/-! ## Derived order lemmas

The transitivity-mixing and strict-combination facts `linarith` soundness needs,
derived from the class axioms (they are not carrier-specific, so they live here once
rather than as instance fields). -/

/-- `a + c ≤ b + c` from `a ≤ b` (right monotonicity, from the left version). -/
theorem add_le_add_right (a b c : K) (h : a ≤ b) : a + c ≤ b + c := by
  kan_rw [add_comm a c, add_comm b c]
  kan_exact add_le_add_left a b c h

/-- `a < c` from `a ≤ b` and `b < c`. -/
theorem lt_of_le_of_lt (a b c : K) (h₁ : a ≤ b) (h₂ : b < c) : a < c :=
  (lt_iff_le_and_ne a c).mpr (And.intro
    (le_trans a b c h₁ ((lt_iff_le_and_ne b c).mp h₂).1)
    (fun hac => ((lt_iff_le_and_ne b c).mp h₂).2
      (le_antisymm b c ((lt_iff_le_and_ne b c).mp h₂).1 (hac ▸ h₁))))

/-- `a < c` from `a < b` and `b ≤ c`. -/
theorem lt_of_lt_of_le (a b c : K) (h₁ : a < b) (h₂ : b ≤ c) : a < c :=
  (lt_iff_le_and_ne a c).mpr (And.intro
    (le_trans a b c ((lt_iff_le_and_ne a b).mp h₁).1 h₂)
    (fun hac => ((lt_iff_le_and_ne a b).mp h₁).2
      (le_antisymm a b ((lt_iff_le_and_ne a b).mp h₁).1 (hac ▸ h₂))))

/-- `a ≤ a + b` when `b` is nonnegative. -/
theorem le_add_of_nonneg_right (a b : K) (hb : 0 ≤ b) : a ≤ a + b :=
  Eq.mp (congrArg (fun z => z ≤ a + b) (add_zero a)) (add_le_add_left 0 b a hb)

/-- `b ≤ a + b` when `a` is nonnegative. -/
theorem le_add_of_nonneg_left (a b : K) (ha : 0 ≤ a) : b ≤ a + b :=
  Eq.mp (congrArg (fun z => z ≤ a + b) (zero_add b)) (add_le_add_right 0 a b ha)

/-- A sum of nonnegatives is nonnegative. -/
theorem add_nonneg (a b : K) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b :=
  le_trans 0 a (a + b) ha (le_add_of_nonneg_right a b hb)

/-- A nonnegative plus a positive is positive. -/
theorem add_pos_of_nonneg_of_pos (a b : K) (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b :=
  lt_of_lt_of_le 0 b (a + b) hb (le_add_of_nonneg_left a b ha)

/-- A positive plus a nonnegative is positive. -/
theorem add_pos_of_pos_of_nonneg (a b : K) (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b :=
  lt_of_lt_of_le 0 a (a + b) ha (le_add_of_nonneg_right a b hb)

/-- A sum of positives is positive. -/
theorem add_pos (a b : K) (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
  add_pos_of_nonneg_of_pos a b (le_of_lt 0 a ha) hb

/-- `a + c < b + c` from `a < b` (right strict monotonicity). -/
theorem add_lt_add_right (a b c : K) (h : a < b) : a + c < b + c := by
  kan_rw [add_comm a c, add_comm b c]
  kan_exact add_lt_add_left a b c h

/-- Right distributivity, from the left version via commutativity. -/
theorem add_mul (a b c : K) : (a + b) * c = a * c + b * c := by
  kan_rw [mul_comm (a + b) c, mul_add c a b, mul_comm c a, mul_comm c b]

/-- Left-commutativity of addition. -/
theorem add_left_comm (a b c : K) : a + (b + c) = b + (a + c) :=
  ((add_assoc a b c).symm.trans (congrArg (· + c) (add_comm a b))).trans (add_assoc b a c)

/-- `a + -a = 0` (right inverse, from the left axiom). -/
theorem add_neg_cancel' (a : K) : a + -a = 0 :=
  (add_comm a (-a)).trans (neg_add_cancel a)

/-- From `a ≤ b`, the difference `b - a` is nonnegative. -/
theorem sub_nonneg_of_le (a b : K) (h : a ≤ b) : 0 ≤ b - a :=
  Eq.mp ((congrArg (fun x => x ≤ b + -a) (add_neg_cancel' a)).trans
      (congrArg (fun y => (0 : K) ≤ y) (sub_eq_add_neg b a).symm))
    (add_le_add_right a b (-a) h)

/-- From `a < b`, the difference `b - a` is positive. -/
theorem sub_pos_of_lt (a b : K) (h : a < b) : 0 < b - a :=
  Eq.mp ((congrArg (fun x => x < b + -a) (add_neg_cancel' a)).trans
      (congrArg (fun y => (0 : K) < y) (sub_eq_add_neg b a).symm))
    (add_lt_add_right a b (-a) h)

/-- `0 * a = 0` (from `a * 0 = 0` via commutativity). -/
theorem zero_mul (a : K) : 0 * a = 0 := (mul_comm 0 a).trans (mul_zero a)

/-- In an additive group, a left-cancelling summand is the negation. -/
theorem neg_eq_of_add_eq_zero (a b : K) (h : a + b = 0) : a = -b :=
  ((add_zero a).symm.trans (congrArg (a + ·) (add_neg_cancel' b).symm)).trans
    (((add_assoc a b (-b)).symm).trans ((congrArg (· + -b) h).trans (zero_add (-b))))

/-- `(-a) * b = -(a * b)`. -/
theorem neg_mul (a b : K) : (-a) * b = -(a * b) :=
  neg_eq_of_add_eq_zero ((-a) * b) (a * b)
    (((add_mul (-a) a b).symm.trans (congrArg (· * b) (neg_add_cancel a))).trans (zero_mul b))

/-- `a * (-b) = -(a * b)`. -/
theorem mul_neg (a b : K) : a * (-b) = -(a * b) :=
  neg_eq_of_add_eq_zero (a * (-b)) (a * b)
    (((mul_add a (-b) b).symm.trans (congrArg (a * ·) (neg_add_cancel b))).trans (mul_zero a))

/-! ## Evaluation of a `LinForm` over an ordered field

The Int-coefficient form is interpreted through the order-preserving cast `ℤ → K`. -/

end OrderedField

/-- Evaluate the linear part of a form over an ordered-field environment, casting each
integer coefficient through `ℤ → K`. -/
def sumTermsK {K : Type} [OrderedField K] (env : Var → K) : List (Int × Var) → K
  | []             => 0
  | (c, v) :: rest => (c : K) * env v + sumTermsK env rest

/-- Evaluate a linear form over an ordered-field environment. -/
def LinForm.evalK {K : Type} [OrderedField K] (env : Var → K) (f : LinForm) : K :=
  sumTermsK env f.terms + (f.const : K)

/-- A fact holds over an ordered-field environment when its form satisfies the asserted
relation with `0`.  Unlike the integer `Fact.holds`, the `<` case stays genuinely strict
(`linarith` does not tighten strict inequalities), which is what keeps systems satisfiable
over a field — e.g. `0 < x ∧ x < 1` — from being refuted. -/
def Fact.holdsK {K : Type} [OrderedField K] (env : Var → K) (fact : Fact) : Prop :=
  match fact.rel with
  | .eq => fact.form.evalK env = 0
  | .le => 0 ≤ fact.form.evalK env
  | .lt => 0 < fact.form.evalK env

namespace OrderedField

variable {K : Type} [OrderedField K]

/-- `sumTermsK` is additive over list append (the keystone induction). -/
theorem sumTermsK_append (env : Var → K) (l1 l2 : List (Int × Var)) :
    sumTermsK env (l1 ++ l2) = sumTermsK env l1 + sumTermsK env l2 := by
  kan_refine (List.rec (motive := fun L =>
    sumTermsK env (L ++ l2) = sumTermsK env L + sumTermsK env l2) ?nil ?cons l1)
  · kan_exact (zero_add (sumTermsK env l2)).symm
  · kan_intro head
    kan_intro tail
    kan_intro ih
    kan_exact ((congrArg (fun x => (head.1 : K) * env head.2 + x) ih).trans
      (add_assoc ((head.1 : K) * env head.2) (sumTermsK env tail) (sumTermsK env l2)).symm)

/-- `evalK` is additive over `LinForm.add`. -/
theorem evalK_add (env : Var → K) (f g : LinForm) :
    (f.add g).evalK env = f.evalK env + g.evalK env := by
  kan_exact ((congrArg (fun x => x + ((f.const + g.const : Int) : K))
      (sumTermsK_append env f.terms g.terms)).trans
    ((congrArg (fun x => sumTermsK env f.terms + sumTermsK env g.terms + x)
        (intCast_add f.const g.const)).trans
      (((add_assoc (sumTermsK env f.terms) (sumTermsK env g.terms)
          ((f.const : K) + (g.const : K)))).trans
        ((congrArg (fun x => sumTermsK env f.terms + x)
            (((add_assoc (sumTermsK env g.terms) (f.const : K) (g.const : K)).symm).trans
              ((congrArg (fun y => y + (g.const : K))
                  (add_comm (sumTermsK env g.terms) (f.const : K))).trans
                (add_assoc (f.const : K) (sumTermsK env g.terms) (g.const : K))))).trans
          (add_assoc (sumTermsK env f.terms) (f.const : K)
            (sumTermsK env g.terms + (g.const : K))).symm))))

/-- `sumTermsK` commutes with scaling all coefficients. -/
theorem sumTermsK_scale (env : Var → K) (k : Int) (l : List (Int × Var)) :
    sumTermsK env (l.map (fun t => (k * t.1, t.2))) = (k : K) * sumTermsK env l := by
  kan_refine (List.rec (motive := fun L =>
    sumTermsK env (L.map (fun t => (k * t.1, t.2))) = (k : K) * sumTermsK env L) ?nil ?cons l)
  · kan_exact (mul_zero (k : K)).symm
  · kan_intro head
    kan_intro tail
    kan_intro ih
    kan_exact ((congrArg (fun x => ((k * head.1 : Int) : K) * env head.2 + x) ih).trans
      ((congrArg (fun y => y * env head.2 + (k : K) * sumTermsK env tail)
          (intCast_mul k head.1)).trans
        ((congrArg (fun y => y + (k : K) * sumTermsK env tail)
            (mul_assoc (k : K) (head.1 : K) (env head.2))).trans
          (mul_add (k : K) ((head.1 : K) * env head.2) (sumTermsK env tail)).symm)))

/-- `evalK` commutes with `LinForm.scale`. -/
theorem evalK_scale (env : Var → K) (k : Int) (f : LinForm) :
    (f.scale k).evalK env = (k : K) * f.evalK env := by
  kan_exact ((congrArg (fun x => x + ((k * f.const : Int) : K))
      (sumTermsK_scale env k f.terms)).trans
    ((congrArg (fun x => (k : K) * sumTermsK env f.terms + x) (intCast_mul k f.const)).trans
      (mul_add (k : K) (sumTermsK env f.terms) (f.const : K)).symm))

/-- A constant form evaluates to (the cast of) its constant. -/
theorem evalK_const (env : Var → K) (c : Int) :
    (LinForm.mk [] c).evalK env = (c : K) :=
  zero_add (c : K)

/-- A single-variable unit form evaluates to that variable's value. -/
theorem evalK_atom (env : Var → K) (v : Var) :
    (LinForm.mk [(1, v)] 0).evalK env = env v := by
  kan_exact ((congrArg (fun x => ((1 : Int) : K) * env v + 0 + x) intCast_zero).trans
    ((add_zero (((1 : Int) : K) * env v + 0)).trans
      ((add_zero (((1 : Int) : K) * env v)).trans
        ((congrArg (fun y => y * env v) intCast_one).trans (one_mul (env v))))))

/-! ## Farkas soundness over an ordered field

The replay folds a refutation certificate `∑ cᵢ · factᵢ` into a proof that the folded
form is nonnegative (or positive, when a strict fact contributes with a positive
coefficient), then derives `False` from a negative (resp. nonpositive) constant residue.
Scaling is by nonnegative integers; a strict fact scaled by a *positive* coefficient
stays strict, and a nonnegative summed with a positive is positive — this is the only
structural departure from the integer leg, which has no strict facts after tightening. -/

/-- Scaling a `≤`-form by a nonnegative integer preserves `0 ≤ evalK`. -/
theorem holdsK_le_scale (env : Var → K) (k : Int) (f : LinForm)
    (hk : 0 ≤ k) (hf : 0 ≤ f.evalK env) : 0 ≤ (f.scale k).evalK env := by
  kan_exact ((evalK_scale env k f).symm ▸
    mul_nonneg (k : K) (f.evalK env) (intCast_nonneg k hk) hf)

/-- Scaling a `<`-form by a positive integer preserves `0 < evalK` (no tightening). -/
theorem holdsK_lt_scale_pos (env : Var → K) (k : Int) (f : LinForm)
    (hk : 0 < k) (hf : 0 < f.evalK env) : 0 < (f.scale k).evalK env := by
  kan_exact ((evalK_scale env k f).symm ▸
    mul_pos (k : K) (f.evalK env) (intCast_pos k hk) hf)

/-- Adding two `≤`-forms preserves `0 ≤ evalK`. -/
theorem holdsK_le_add (env : Var → K) (f g : LinForm)
    (hf : 0 ≤ f.evalK env) (hg : 0 ≤ g.evalK env) : 0 ≤ (f.add g).evalK env := by
  kan_exact ((evalK_add env f g).symm ▸ add_nonneg (f.evalK env) (g.evalK env) hf hg)

/-- A nonnegative `≤`-form plus a positive `<`-form is positive. -/
theorem holdsK_lt_add_of_le_of_lt (env : Var → K) (f g : LinForm)
    (hf : 0 ≤ f.evalK env) (hg : 0 < g.evalK env) : 0 < (f.add g).evalK env := by
  kan_exact ((evalK_add env f g).symm ▸
    add_pos_of_nonneg_of_pos (f.evalK env) (g.evalK env) hf hg)

/-- A positive `<`-form plus a nonnegative `≤`-form is positive. -/
theorem holdsK_lt_add_of_lt_of_le (env : Var → K) (f g : LinForm)
    (hf : 0 < f.evalK env) (hg : 0 ≤ g.evalK env) : 0 < (f.add g).evalK env := by
  kan_exact ((evalK_add env f g).symm ▸
    add_pos_of_pos_of_nonneg (f.evalK env) (g.evalK env) hf hg)

/-- A sum of two positive `<`-forms is positive. -/
theorem holdsK_lt_add (env : Var → K) (f g : LinForm)
    (hf : 0 < f.evalK env) (hg : 0 < g.evalK env) : 0 < (f.add g).evalK env := by
  kan_exact ((evalK_add env f g).symm ▸ add_pos (f.evalK env) (g.evalK env) hf hg)

/-! ## Per-hypothesis bridges with denominator clearing

A `ℚ` hypothesis `lhs R rhs` is reified by clearing denominators: the verified reifier
produces a positive integer `d` and an integer-coefficient form with the proof
`(d : K) * (rhs - lhs) = form.evalK env`.  Since `d > 0`, scaling preserves the sign of
`rhs - lhs`, so `lhs ≤ rhs` yields `0 ≤ form` and `lhs < rhs` yields `0 < form` — the
strict case is *not* tightened. -/

/-- From `lhs ≤ rhs` and a denominator-clearing reification, the cleared form is
nonnegative. -/
theorem holdsK_le_of_diff (env : Var → K) (form : LinForm) (d : Int) (lhs rhs : K)
    (p : (d : K) * (rhs - lhs) = form.evalK env) (hd : 0 < d) (hyp : lhs ≤ rhs) :
    0 ≤ form.evalK env :=
  p ▸ mul_nonneg (d : K) (rhs - lhs) (le_of_lt 0 (d : K) (intCast_pos d hd))
    (sub_nonneg_of_le lhs rhs hyp)

/-- From `lhs < rhs` and a denominator-clearing reification, the cleared form is positive
(strictness preserved). -/
theorem holdsK_lt_of_diff (env : Var → K) (form : LinForm) (d : Int) (lhs rhs : K)
    (p : (d : K) * (rhs - lhs) = form.evalK env) (hd : 0 < d) (hyp : lhs < rhs) :
    0 < form.evalK env :=
  p ▸ mul_pos (d : K) (rhs - lhs) (intCast_pos d hd) (sub_pos_of_lt lhs rhs hyp)

/-! ## Term collection over an ordered field

The collapse machinery (`insertTerm`/`collapse`/`isZeroCoeff`, from `Core.Collapse`) is
carrier-agnostic; only the `sumTermsK` soundness lemmas are reproved here. -/

/-- Inserting a term shifts `sumTermsK` by that term's contribution. -/
theorem insert_evalK (env : Var → K) (t : Int × Var) (l : List (Int × Var)) :
    sumTermsK env (insertTerm t l) = (t.1 : K) * env t.2 + sumTermsK env l := by
  kan_refine (List.rec (motive := fun L =>
    sumTermsK env (insertTerm t L) = (t.1 : K) * env t.2 + sumTermsK env L) ?nil ?cons l)
  · kan_rfl
  · kan_intro head
    kan_intro tail
    kan_intro ih
    kan_by_cases hv : (t.2 == head.2) = true
    · kan_exact ((congrArg (sumTermsK env) (if_pos hv)).trans
        ((congrArg (fun z => z * env head.2 + sumTermsK env tail) (intCast_add t.1 head.1)).trans
          ((congrArg (fun x => x + sumTermsK env tail)
              (add_mul (t.1 : K) (head.1 : K) (env head.2))).trans
            ((add_assoc ((t.1 : K) * env head.2) ((head.1 : K) * env head.2)
                (sumTermsK env tail)).trans
              (congrArg (fun w => (t.1 : K) * env w
                  + ((head.1 : K) * env head.2 + sumTermsK env tail))
                (eq_of_beq hv).symm)))))
    · kan_exact ((congrArg (sumTermsK env) (if_neg hv)).trans
        ((congrArg (fun x => (head.1 : K) * env head.2 + x) ih).trans
          (add_left_comm ((head.1 : K) * env head.2) ((t.1 : K) * env t.2)
            (sumTermsK env tail))))

/-- Collapsing preserves `sumTermsK`. -/
theorem collapse_evalK (env : Var → K) (terms : List (Int × Var)) :
    sumTermsK env (collapse terms) = sumTermsK env terms := by
  kan_refine (List.rec (motive := fun L =>
    sumTermsK env (collapse L) = sumTermsK env L) ?nil ?cons terms)
  · kan_rfl
  · kan_intro head
    kan_intro tail
    kan_intro ih
    kan_exact ((insert_evalK env head (collapse tail)).trans
      (congrArg (fun x => (head.1 : K) * env head.2 + x) ih))

/-- An all-zero-coefficient term list sums to `0`. -/
theorem sumTermsK_allZero (env : Var → K) (terms : List (Int × Var)) :
    terms.all isZeroCoeff = true → sumTermsK env terms = 0 := by
  kan_refine (List.rec (motive := fun L =>
    L.all isZeroCoeff = true → sumTermsK env L = 0) ?nil ?cons terms)
  · kan_intro h0
    kan_rfl
  · kan_intro head
    kan_intro tail
    kan_intro ih
    kan_intro hcons
    kan_exact ((congrArg (fun c : Int => (c : K) * env head.2 + sumTermsK env tail)
        (eq_of_beq (Bool.and_eq_true_iff.mp hcons).1)).trans
      ((congrArg (fun x => x + sumTermsK env tail)
          ((congrArg (fun z => z * env head.2) intCast_zero).trans (zero_mul (env head.2)))).trans
        ((zero_add (sumTermsK env tail)).trans (ih (Bool.and_eq_true_iff.mp hcons).2))))

/-- If a form's terms collapse to all-zero coefficients, it evaluates to its constant. -/
theorem evalK_eq_const_of_collapse (env : Var → K) (f : LinForm)
    (h : (collapse f.terms).all isZeroCoeff = true) : f.evalK env = (f.const : K) := by
  kan_exact ((congrArg (fun s => s + (f.const : K))
      ((collapse_evalK env f.terms).symm.trans (sumTermsK_allZero env (collapse f.terms) h))).trans
    (zero_add (f.const : K)))

/-! ## Refutation closers

A folded combination whose variable terms collapse to all-zero and whose constant residue
contradicts the asserted relation is `False`. -/

/-- `≤` residual: nonnegative folded form, all-zero variable terms, negative constant. -/
theorem falseK_of_fold (env : Var → K) (f : LinForm)
    (foldedProof : 0 ≤ f.evalK env)
    (hCollapse : (collapse f.terms).all isZeroCoeff = true)
    (hneg : f.const < 0) : False :=
  absurd (evalK_eq_const_of_collapse env f hCollapse ▸ foldedProof)
    ((not_le 0 (f.const : K)).mpr ((intCast_zero (K := K)) ▸ intCast_lt f.const 0 hneg))

/-- `<` residual: positive folded form, all-zero variable terms, nonpositive constant.
The strict analogue of `falseK_of_fold`, with no counterpart in the integer leg. -/
theorem falseK_of_fold_lt (env : Var → K) (f : LinForm)
    (foldedProof : 0 < f.evalK env)
    (hCollapse : (collapse f.terms).all isZeroCoeff = true)
    (hnonpos : f.const ≤ 0) : False :=
  absurd ((intCast_zero (K := K)) ▸ intCast_le f.const 0 hnonpos)
    ((not_le (f.const : K) 0).mpr (evalK_eq_const_of_collapse env f hCollapse ▸ foldedProof))

/-- The empty form is nonnegative (the certificate-fold accumulator's base case; unlike
`ℤ`, `ℚ` addition is irreducible so this is not definitional). -/
theorem evalK_nil_nonneg (env : Var → K) : 0 ≤ (LinForm.mk [] 0).evalK env :=
  Eq.mpr (congrArg (fun z => (0 : K) ≤ z)
    ((evalK_const env 0).trans intCast_zero)) (le_refl 0)

/-! ## Reify bridges (denominator clearing)

The verified `ℚ` reifier produces, for an expression `e`, an integer-coefficient form
and a positive denominator `d` with `(d : K) * e = form.evalK env`.  These bridges are
the per-constructor steps it composes; `d` accumulates as the product of the denominators
introduced by division, so the engine only ever sees integer-coefficient constraints. -/

/-- A form scaled by `-1` evaluates to the negation. -/
theorem evalK_scale_neg_one (env : Var → K) (fa : LinForm) :
    (fa.scale (-1)).evalK env = -(fa.evalK env) :=
  (evalK_scale env (-1) fa).trans
    ((congrArg (fun z => z * fa.evalK env)
        ((intCast_neg 1).trans (congrArg (fun w => -w) intCast_one))).trans
      ((neg_mul (1 : K) (fa.evalK env)).trans (congrArg (fun z => -z) (one_mul (fa.evalK env)))))

/-- Atom: denominator `1`. -/
theorem reifyQ_atom (env : Var → K) (v : Var) :
    ((1 : Int) : K) * env v = (LinForm.mk [(1, v)] 0).evalK env :=
  ((congrArg (fun z => z * env v) intCast_one).trans (one_mul (env v))).trans
    (evalK_atom env v).symm

/-- Integer constant: denominator `1`. -/
theorem reifyQ_const (env : Var → K) (c : Int) :
    ((1 : Int) : K) * (c : K) = (LinForm.mk [] c).evalK env :=
  ((congrArg (fun z => z * (c : K)) intCast_one).trans (one_mul (c : K))).trans
    (evalK_const env c).symm

/-- Negation: denominator unchanged. -/
theorem reifyQ_neg (env : Var → K) (fa : LinForm) (d : Int) (a : K)
    (pa : (d : K) * a = fa.evalK env) :
    (d : K) * (-a) = (fa.scale (-1)).evalK env :=
  (mul_neg (d : K) a).trans
    ((congrArg (fun z => -z) pa).trans (evalK_scale_neg_one env fa).symm)

/-- Multiplication by an integer-literal coefficient: denominator unchanged. -/
theorem reifyQ_mul_const (env : Var → K) (fa : LinForm) (d : Int) (a : K) (k : Int)
    (pa : (d : K) * a = fa.evalK env) :
    (d : K) * (((k : Int) : K) * a) = (fa.scale k).evalK env :=
  ((mul_assoc (d : K) ((k : Int) : K) a).symm.trans
      (congrArg (fun z => z * a) (mul_comm (d : K) ((k : Int) : K)))).trans
    ((mul_assoc ((k : Int) : K) (d : K) a).trans
      ((congrArg (fun z => ((k : Int) : K) * z) pa).trans (evalK_scale env k fa).symm))

/-- Division by a nonzero integer-literal: denominator multiplied by the divisor. -/
theorem reifyQ_div (env : Var → K) (fa : LinForm) (d : Int) (a : K) (k : Int)
    (hk : ((k : Int) : K) ≠ 0) (pa : (d : K) * a = fa.evalK env) :
    ((d * k : Int) : K) * (a / ((k : Int) : K)) = fa.evalK env :=
  (congrArg (fun z => z * (a / ((k : Int) : K))) (intCast_mul d k)).trans
    ((mul_assoc (d : K) ((k : Int) : K) (a / ((k : Int) : K))).trans
      ((congrArg (fun z => (d : K) * z)
          ((mul_comm ((k : Int) : K) (a / ((k : Int) : K))).trans
            (div_mul_cancel a ((k : Int) : K) hk))).trans pa))

/-- Sum: the denominators multiply. -/
theorem reifyQ_add (env : Var → K) (fa fb : LinForm) (da db : Int) (a b : K)
    (pa : (da : K) * a = fa.evalK env) (pb : (db : K) * b = fb.evalK env) :
    ((da * db : Int) : K) * (a + b) = ((fa.scale db).add (fb.scale da)).evalK env :=
  (mul_add ((da * db : Int) : K) a b).trans
    ((congrArg (fun z => z + ((da * db : Int) : K) * b)
        (((congrArg (fun z => z * a) (intCast_mul da db)).trans
            ((congrArg (fun z => z * a) (mul_comm (da : K) (db : K))).trans
              ((mul_assoc (db : K) (da : K) a).trans
                (congrArg (fun z => (db : K) * z) pa)))).trans
          (evalK_scale env db fa).symm)).trans
      ((congrArg (fun z => (fa.scale db).evalK env + z)
          (((congrArg (fun z => z * b) (intCast_mul da db)).trans
              ((mul_assoc (da : K) (db : K) b).trans
                (congrArg (fun z => (da : K) * z) pb))).trans
            (evalK_scale env da fb).symm)).trans
        (evalK_add env (fa.scale db) (fb.scale da)).symm))

/-- Difference: the denominators multiply, the subtrahend form is negated. -/
theorem reifyQ_sub (env : Var → K) (fa fb : LinForm) (da db : Int) (a b : K)
    (pa : (da : K) * a = fa.evalK env) (pb : (db : K) * b = fb.evalK env) :
    ((da * db : Int) : K) * (a - b) = ((fa.scale db).add (fb.scale (-da))).evalK env :=
  let t1 : ((da * db : Int) : K) * a = (fa.scale db).evalK env :=
    ((congrArg (fun z => z * a) (intCast_mul da db)).trans
        ((congrArg (fun z => z * a) (mul_comm (da : K) (db : K))).trans
          ((mul_assoc (db : K) (da : K) a).trans
            (congrArg (fun z => (db : K) * z) pa)))).trans
      (evalK_scale env db fa).symm
  let t2 : ((da * db : Int) : K) * (-b) = (fb.scale (-da)).evalK env :=
    ((congrArg (fun z => z * (-b)) (intCast_mul da db)).trans
        ((mul_assoc (da : K) (db : K) (-b)).trans
          ((congrArg (fun z => (da : K) * z) (mul_neg (db : K) b)).trans
            ((congrArg (fun z => (da : K) * (-z)) pb).trans
              (mul_neg (da : K) (fb.evalK env)))))).trans
      ((evalK_scale env (-da) fb).trans
        ((congrArg (fun z => z * fb.evalK env) (intCast_neg da)).trans
          (neg_mul (da : K) (fb.evalK env)))).symm
  (congrArg (fun z => ((da * db : Int) : K) * z) (sub_eq_add_neg a b)).trans
    ((mul_add ((da * db : Int) : K) a (-b)).trans
      ((congrArg (fun z => z + ((da * db : Int) : K) * (-b)) t1).trans
        ((congrArg (fun z => (fa.scale db).evalK env + z) t2).trans
          (evalK_add env (fa.scale db) (fb.scale (-da))).symm)))

end OrderedField
end KanSaturation
