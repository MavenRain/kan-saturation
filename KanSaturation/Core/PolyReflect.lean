import KanSaturation.Core.Constraint
import KanTactics

/-!
# `KanSaturation.Core.PolyReflect`

The **polynomial soundness substrate**: the reflective denotation a Positivstellensatz /
ideal-membership certificate replays through, the multivariate analogue of the linear
`Core.Eval` + `Core.Collapse` bootstrap, but over rational (`ℚ`) coefficients.

A `MvPoly` is a sum of `Mono`mial terms, each a `Rat` coefficient times a power-product
(an exponent vector `List (Var × Nat)`).  Polynomial multiplication is realized by
*concatenating* exponent vectors (never merging/sorting), so the eval bridge to a product
needs only `evalVars_append` — there is no `pow_add` obligation.  This keeps the entire
substrate inside the confirmed Mathlib-free `Rat.*` lemma surface.

Per the project convention every proof here is **kan-tactics only** (no
`simp`/`rw`/`ring`/`omega`/`linarith`/`decide`): this is the irreducible polynomial
arithmetic bootstrap.  As in `Core.Eval`, `kan_induction` cannot infer the motive for these
goals, so the recursor is applied explicitly via `kan_refine (List.rec (motive := …) …)` and
each case is closed by `kan_exact` of an explicit proof term (the constructor reductions of
`evalVars`/`sumTermsP`/`++`/`List.map`/`List.foldr` hold definitionally, so no `dsimp` is
needed).
-/

namespace KanSaturation

/-- `b ^ n` over ℚ by structural recursion (monomial denotation; never on the replay path). -/
def powNat (b : Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => powNat b n * b

/-- Evaluate a power-product `∏ xᵥ ^ e` under an environment. -/
def evalVars (env : Var → Rat) : List (Var × Nat) → Rat
  | [] => 1
  | (v, e) :: rest => powNat (env v) e * evalVars env rest

/-- A monomial term: a rational coefficient times a power-product (exponent vector). -/
structure Mono where
  coeff : Rat
  vars : List (Var × Nat)
  deriving Repr, Inhabited, BEq, DecidableEq

def Mono.eval (env : Var → Rat) (m : Mono) : Rat := m.coeff * evalVars env m.vars

/-- A multivariate polynomial: a sum of monomial terms (duplicates tolerated until normalize). -/
structure MvPoly where
  terms : List Mono
  deriving Repr, Inhabited, BEq, DecidableEq

def sumTermsP (env : Var → Rat) : List Mono → Rat
  | [] => 0
  | m :: rest => m.eval env + sumTermsP env rest

def MvPoly.eval (env : Var → Rat) (p : MvPoly) : Rat := sumTermsP env p.terms

def MvPoly.zero : MvPoly := ⟨[]⟩
def MvPoly.one : MvPoly := ⟨[⟨1, []⟩]⟩
def MvPoly.const (c : Rat) : MvPoly := ⟨[⟨c, []⟩]⟩
def MvPoly.atom (v : Var) : MvPoly := ⟨[⟨1, [(v, 1)]⟩]⟩
def MvPoly.add (p q : MvPoly) : MvPoly := ⟨p.terms ++ q.terms⟩
/-- Multiply polynomial `p` by a single monomial term `m`. CONCATENATION of exponent
vectors (`m.vars ++ t.vars`), never merge/sort — this is what keeps the eval bridge to
just `evalVars_append` (no `pow_add`). -/
def MvPoly.scaleMono (m : Mono) (p : MvPoly) : MvPoly :=
  ⟨p.terms.map (fun t => ⟨m.coeff * t.coeff, m.vars ++ t.vars⟩)⟩
def MvPoly.scale (k : Rat) (p : MvPoly) : MvPoly := p.scaleMono ⟨k, []⟩
def MvPoly.neg (p : MvPoly) : MvPoly := p.scale (-1)
def MvPoly.mul (p q : MvPoly) : MvPoly :=
  p.terms.foldr (fun m acc => (q.scaleMono m).add acc) MvPoly.zero
def MvPoly.sub (p q : MvPoly) : MvPoly := p.add q.neg

/-! ## Arithmetic helper

`Rat.neg_one_mul` is absent Mathlib-free, so `-1 * x = -x` is derived where needed from
`Rat.neg_mul` + `Rat.one_mul`.  The single shared rearrangement helper below is the
monomial-multiply analogue of the linear leg's reassociation. -/

/-- The product reassociation `eval_scaleMono` needs: `(a * b) * (c * d) = (a * c) * (b * d)`.
Derived from `Rat.mul_assoc` / `Rat.mul_comm`. -/
theorem mul_swap (a b c d : Rat) : (a * b) * (c * d) = (a * c) * (b * d) :=
  (Rat.mul_assoc a b (c * d)).trans
    ((congrArg (fun z => a * z)
        ((Rat.mul_assoc b c d).symm.trans
          ((congrArg (fun z => z * d) (Rat.mul_comm b c)).trans (Rat.mul_assoc c b d)))).trans
      (Rat.mul_assoc a c (b * d)).symm)

/-! ## Evaluation homomorphism lemmas -/

/-- `evalVars` is multiplicative over exponent-vector append (the keystone induction;
the monomial analogue of `sumTerms_append`). -/
theorem evalVars_append (env : Var → Rat) (l1 l2 : List (Var × Nat)) :
    evalVars env (l1 ++ l2) = evalVars env l1 * evalVars env l2 := by
  kan_refine (List.rec (motive := fun L =>
    evalVars env (L ++ l2) = evalVars env L * evalVars env l2) ?nil ?cons l1)
  · kan_exact (Rat.one_mul (evalVars env l2)).symm
  · kan_intro head
    kan_intro tail
    kan_intro ih
    kan_exact ((congrArg (fun x => powNat (env head.1) head.2 * x) ih).trans
      (Rat.mul_assoc (powNat (env head.1) head.2) (evalVars env tail) (evalVars env l2)).symm)

/-- `sumTermsP` is additive over list append (exact mirror of `sumTerms_append`). -/
theorem sumTermsP_append (env : Var → Rat) (l1 l2 : List Mono) :
    sumTermsP env (l1 ++ l2) = sumTermsP env l1 + sumTermsP env l2 := by
  kan_refine (List.rec (motive := fun L =>
    sumTermsP env (L ++ l2) = sumTermsP env L + sumTermsP env l2) ?nil ?cons l1)
  · kan_exact (Rat.zero_add (sumTermsP env l2)).symm
  · kan_intro head
    kan_intro tail
    kan_intro ih
    kan_exact ((congrArg (fun x => head.eval env + x) ih).trans
      (Rat.add_assoc (head.eval env) (sumTermsP env tail) (sumTermsP env l2)).symm)

/-- `eval` is additive over `MvPoly.add` (defeq to `sumTermsP_append`). -/
theorem MvPoly.eval_add (env : Var → Rat) (p q : MvPoly) :
    (p.add q).eval env = p.eval env + q.eval env :=
  sumTermsP_append env p.terms q.terms

/-- `eval` of a monomial-scaled polynomial factors the monomial out (the product keystone).
Cons step uses `evalVars_append` + `mul_swap` + `Rat.mul_add`; base uses `Rat.mul_zero`. -/
theorem MvPoly.eval_scaleMono (env : Var → Rat) (m : Mono) (p : MvPoly) :
    (p.scaleMono m).eval env = m.eval env * p.eval env := by
  kan_refine (List.rec (motive := fun L =>
    sumTermsP env (L.map (fun t => (⟨m.coeff * t.coeff, m.vars ++ t.vars⟩ : Mono)))
      = m.eval env * sumTermsP env L) ?nil ?cons p.terms)
  · kan_exact (Rat.mul_zero (m.eval env)).symm
  · kan_intro head
    kan_intro tail
    kan_intro ih
    kan_exact ((congrArg
        (fun x => (m.coeff * head.coeff) * evalVars env (m.vars ++ head.vars) + x) ih).trans
      ((congrArg
          (fun y => (m.coeff * head.coeff) * y + m.eval env * sumTermsP env tail)
          (evalVars_append env m.vars head.vars)).trans
        ((congrArg (fun y => y + m.eval env * sumTermsP env tail)
            (mul_swap m.coeff head.coeff (evalVars env m.vars) (evalVars env head.vars))).trans
          (Rat.mul_add (m.coeff * evalVars env m.vars)
            (head.coeff * evalVars env head.vars) (sumTermsP env tail)).symm)))

/-- `eval` is multiplicative over `MvPoly.mul`.  Single induction on `p.terms` (the `foldr`);
cons step uses `eval_add` + `eval_scaleMono` + `Rat.add_mul`.  No nested induction. -/
theorem MvPoly.eval_mul (env : Var → Rat) (p q : MvPoly) :
    (p.mul q).eval env = p.eval env * q.eval env := by
  kan_refine (List.rec (motive := fun L =>
    (List.foldr (fun m acc => (q.scaleMono m).add acc) MvPoly.zero L).eval env
      = sumTermsP env L * q.eval env) ?nil ?cons p.terms)
  · kan_exact (Rat.zero_mul (q.eval env)).symm
  · kan_intro head
    kan_intro tail
    kan_intro ih
    kan_exact ((MvPoly.eval_add env (q.scaleMono head)
        (List.foldr (fun m acc => (q.scaleMono m).add acc) MvPoly.zero tail)).trans
      ((congrArg (fun x => x
          + (List.foldr (fun m acc => (q.scaleMono m).add acc) MvPoly.zero tail).eval env)
          (MvPoly.eval_scaleMono env head q)).trans
        ((congrArg (fun x => head.eval env * q.eval env + x) ih).trans
          (Rat.add_mul (head.eval env) (sumTermsP env tail) (q.eval env)).symm)))

/-- `eval` commutes with scalar scaling (`Rat.mul_one` collapses `k * 1`). -/
theorem MvPoly.eval_scale (env : Var → Rat) (k : Rat) (p : MvPoly) :
    (p.scale k).eval env = k * p.eval env :=
  (MvPoly.eval_scaleMono env ⟨k, []⟩ p).trans
    (congrArg (fun z => z * p.eval env) (Rat.mul_one k))

/-- `eval` of the negation is the negation (`-1 * x = -x` derived from `Rat.neg_mul`). -/
theorem MvPoly.eval_neg (env : Var → Rat) (p : MvPoly) :
    (p.neg).eval env = - p.eval env :=
  (MvPoly.eval_scale env (-1) p).trans
    ((Rat.neg_mul 1 (p.eval env)).trans (congrArg (fun z => -z) (Rat.one_mul (p.eval env))))

/-- The zero polynomial evaluates to `0`. -/
theorem MvPoly.eval_zero (env : Var → Rat) : MvPoly.zero.eval env = 0 := by
  kan_rfl

/-- A constant polynomial evaluates to its constant (`c * 1 + 0`). -/
theorem MvPoly.eval_const (env : Var → Rat) (c : Rat) :
    (MvPoly.const c).eval env = c :=
  (Rat.add_zero (c * 1)).trans (Rat.mul_one c)

/-- An atom polynomial evaluates to that variable's value (`1 * ((1 * env v) * 1) + 0`). -/
theorem MvPoly.eval_atom (env : Var → Rat) (v : Var) :
    (MvPoly.atom v).eval env = env v :=
  (Rat.add_zero (1 * ((1 * env v) * 1))).trans
    ((Rat.one_mul ((1 * env v) * 1)).trans
      ((Rat.mul_one (1 * env v)).trans (Rat.one_mul (env v))))

/-- `eval` commutes with subtraction (`eval_add` + `eval_neg` + `Rat.sub_eq_add_neg`). -/
theorem MvPoly.eval_sub (env : Var → Rat) (p q : MvPoly) :
    (p.sub q).eval env = p.eval env - q.eval env :=
  (MvPoly.eval_add env p q.neg).trans
    ((congrArg (fun z => p.eval env + z) (MvPoly.eval_neg env q)).trans
      (Rat.sub_eq_add_neg (p.eval env) (q.eval env)).symm)

/-! ## Equality-fact soundness

The ideal/equality leg replays `a = b` hypotheses: each reifies to `a - b = pᵢ.eval env`,
so the hypothesis gives `pᵢ.eval env = 0`; a certificate cofactor `q` contributes
`q.eval env * pᵢ.eval env = 0`; the cofactor sum is `0`; and a nonzero constant residue
refutes. -/

/-- An equality hypothesis `a = b` makes its reified difference polynomial vanish.
Derived: substitute `hyp` into `pp`, then `Rat.sub_self` (`b - b = 0`). -/
theorem holdsP_of_eq (p : MvPoly) (env : Var → Rat) (a b : Rat)
    (pp : a - b = p.eval env) (hyp : a = b) : p.eval env = 0 :=
  pp.symm.trans ((congrArg (fun x => x - b) hyp).trans (Rat.sub_self (a := b)))

/-- A cofactor times a vanishing polynomial vanishes. -/
theorem holdsP_mul_zero (qe pe : Rat) (h : pe = 0) : qe * pe = 0 :=
  (congrArg (fun z => qe * z) h).trans (Rat.mul_zero qe)

/-- A sum of two vanishing values vanishes. -/
theorem holdsP_add_zero (a b : Rat) (ha : a = 0) (hb : b = 0) : a + b = 0 :=
  (congrArg (fun x => x + b) ha).trans
    ((congrArg (fun y => (0 : Rat) + y) hb).trans (Rat.add_zero (0 : Rat)))

/-- The equality-residue refutation closer: a constant `c ≠ 0` (as the decidable residue
`(c == 0) = false`) whose cast to ℚ is `0` is absurd, via `Rat.intCast_inj`.
The `Bool`/`Int`-shaped side conditions are exactly what an `Expr`-replay caller discharges
with `mkDecideProof`. -/
theorem false_of_const_eval_zero (c : Int) (hc : (c == 0) = false)
    (hzero : ((c : Int) : Rat) = 0) : False :=
  Bool.noConfusion
    (((congrArg (fun z => z == (0 : Int)) (Rat.intCast_inj.mp (hzero.trans Rat.intCast_zero.symm))).trans
        (beq_self_eq_true (0 : Int))).symm.trans hc)

/-! ## Reify bridges

Thin per-constructor bridges the verified `ℚ` polynomial reifier composes; the monomial
analogues of `Core.Eval`'s `reify_*`, with `env` as the leading explicit argument. -/

/-- Reification bridge for addition. -/
theorem reifyP_add (env : Var → Rat) (pa pb : MvPoly) (a b : Rat)
    (pa_eq : a = pa.eval env) (pb_eq : b = pb.eval env) :
    a + b = (pa.add pb).eval env :=
  ((congrArg (fun x => x + b) pa_eq).trans
      (congrArg (fun y => pa.eval env + y) pb_eq)).trans
    (MvPoly.eval_add env pa pb).symm

/-- Reification bridge for subtraction. -/
theorem reifyP_sub (env : Var → Rat) (pa pb : MvPoly) (a b : Rat)
    (pa_eq : a = pa.eval env) (pb_eq : b = pb.eval env) :
    a - b = (pa.sub pb).eval env :=
  ((congrArg (fun x => x - b) pa_eq).trans
      (congrArg (fun y => pa.eval env - y) pb_eq)).trans
    (MvPoly.eval_sub env pa pb).symm

/-- Reification bridge for negation. -/
theorem reifyP_neg (env : Var → Rat) (pa : MvPoly) (a : Rat)
    (pa_eq : a = pa.eval env) :
    -a = (pa.neg).eval env :=
  (congrArg (fun x => -x) pa_eq).trans (MvPoly.eval_neg env pa).symm

/-- Reification bridge for multiplication. -/
theorem reifyP_mul (env : Var → Rat) (pa pb : MvPoly) (a b : Rat)
    (pa_eq : a = pa.eval env) (pb_eq : b = pb.eval env) :
    a * b = (pa.mul pb).eval env :=
  ((congrArg (fun x => x * b) pa_eq).trans
      (congrArg (fun y => pa.eval env * y) pb_eq)).trans
    (MvPoly.eval_mul env pa pb).symm

/-- Reification bridge for a rational constant. -/
theorem reifyP_const (env : Var → Rat) (c : Rat) :
    c = (MvPoly.const c).eval env :=
  (MvPoly.eval_const env c).symm

/-- Reification bridge for an atom. -/
theorem reifyP_atom (env : Var → Rat) (v : Var) :
    env v = (MvPoly.atom v).eval env :=
  (MvPoly.eval_atom env v).symm

/-! ## Term collection (the refutation closer)

The polynomial analogue of `Core.Collapse`.  The replay folds the cofactor combination
`Σ qᵢ·pᵢ` into one `MvPoly` and must read off its constant value soundly.  `collapseP`
merges monomial terms that share the *same raw exponent vector* (summing coefficients),
exactly as the linear `collapse` merges by variable.  Crucially the merge key is the
*unnormalized* `vars` list, so `collapseP_eval` needs only `Rat.add_mul` — no `pow_add`
and no permutation argument (the reifier and cofactor multiplications keep the cancelling
monomials in aligned raw form).  A folded combination that collapses to a single constant
monomial therefore evaluates to that constant, and a nonzero such constant refutes. -/

/-- `a + (b + c) = b + (a + c)` over ℚ (`Rat.add_left_comm` is absent Mathlib-free). -/
theorem add_left_commR (a b c : Rat) : a + (b + c) = b + (a + c) :=
  (Rat.add_assoc a b c).symm.trans
    ((congrArg (fun z => z + c) (Rat.add_comm a b)).trans (Rat.add_assoc b a c))

/-- Insert a monomial term, summing coefficients when the raw exponent vector matches. -/
def insertMono : Mono → List Mono → List Mono
  | m, [] => [m]
  | m, m' :: rest =>
      if m.vars == m'.vars then ⟨m.coeff + m'.coeff, m'.vars⟩ :: rest
      else m' :: insertMono m rest

/-- Collapse like monomial terms by repeated insertion. -/
def collapseP (terms : List Mono) : List Mono := terms.foldr insertMono []

/-- Inserting a term shifts `sumTermsP` by that term's contribution. -/
theorem insertMono_eval (env : Var → Rat) (m : Mono) (l : List Mono) :
    sumTermsP env (insertMono m l) = m.eval env + sumTermsP env l := by
  kan_refine (List.rec (motive := fun L =>
    sumTermsP env (insertMono m L) = m.eval env + sumTermsP env L) ?nil ?cons l)
  · kan_rfl
  · kan_intro head
    kan_intro tail
    kan_intro ih
    kan_by_cases hv : (m.vars == head.vars) = true
    · kan_exact ((congrArg (sumTermsP env) (if_pos hv)).trans
        ((congrArg (fun x => x + sumTermsP env tail)
            (Rat.add_mul m.coeff head.coeff (evalVars env head.vars))).trans
          ((Rat.add_assoc (m.coeff * evalVars env head.vars)
              (head.coeff * evalVars env head.vars) (sumTermsP env tail)).trans
            (congrArg (fun w => m.coeff * evalVars env w
                + (head.coeff * evalVars env head.vars + sumTermsP env tail))
              (eq_of_beq hv).symm))))
    · kan_exact ((congrArg (sumTermsP env) (if_neg hv)).trans
        ((congrArg (fun x => head.eval env + x) ih).trans
          (add_left_commR (head.eval env) (m.eval env) (sumTermsP env tail))))

/-- Collapsing preserves `sumTermsP`. -/
theorem collapseP_eval (env : Var → Rat) (terms : List Mono) :
    sumTermsP env (collapseP terms) = sumTermsP env terms := by
  kan_refine (List.rec (motive := fun L =>
    sumTermsP env (collapseP L) = sumTermsP env L) ?nil ?cons terms)
  · kan_rfl
  · kan_intro head
    kan_intro tail
    kan_intro ih
    kan_exact ((insertMono_eval env head (collapseP tail)).trans
      (congrArg (fun x => head.eval env + x) ih))

/-- If a polynomial's terms collapse to a single constant monomial, it evaluates to that
constant.  This is the collection step the replay applies to the folded combination. -/
theorem eval_const_of_collapseP (env : Var → Rat) (p : MvPoly) (c : Rat)
    (h : collapseP p.terms = [⟨c, []⟩]) : p.eval env = c :=
  ((collapseP_eval env p.terms).symm.trans (congrArg (sumTermsP env) h)).trans
    ((Rat.add_zero (c * 1)).trans (Rat.mul_one c))

/-- The replay's closing step: a folded combination whose value is `0` (forced by every
hypothesis equation), yet which collapses to a single nonzero constant monomial, is a
contradiction.  The elaborator discharges `hc`/`h` with `mkDecideProof`. -/
theorem false_of_collapseP (env : Var → Rat) (p : MvPoly) (c : Rat)
    (hzero : p.eval env = 0) (hc : ¬ (c = 0))
    (h : collapseP p.terms = [⟨c, []⟩]) : False :=
  hc ((eval_const_of_collapseP env p c h).symm.trans hzero)

/-! ## Zero-coefficient cleanup

`collapseP` merges like monomials but **retains** the merged term even when its coefficient
sums to `0` (it never deletes), so a polynomial that is identically zero collapses to a list
of zero-coefficient *ghosts* (e.g. `[⟨0, x²⟩]`), not `[]`.  Replays therefore filter those
ghosts with `dropZeros` before reading off the residue; `dropZeros_eval` shows the filter is
sound (a zero-coefficient monomial contributes `0`).  The ghost-tolerant closers
`false_of_collapseP'` / `prove_eq'` are the versions the elaborator actually uses. -/

/-- Drop monomials whose coefficient is `0` (the ghosts `collapseP` leaves behind). -/
def dropZeros : List Mono → List Mono
  | [] => []
  | m :: rest => if m.coeff == 0 then dropZeros rest else m :: dropZeros rest

/-- A monomial with zero coefficient evaluates to `0` (`Rat.zero_mul`). -/
theorem mono_eval_of_coeff_zero (env : Var → Rat) (m : Mono) (h : m.coeff = 0) :
    m.eval env = 0 :=
  (congrArg (fun z => z * evalVars env m.vars) h).trans (Rat.zero_mul (evalVars env m.vars))

/-- Dropping zero-coefficient ghosts preserves `sumTermsP`. -/
theorem dropZeros_eval (env : Var → Rat) (terms : List Mono) :
    sumTermsP env (dropZeros terms) = sumTermsP env terms := by
  kan_refine (List.rec (motive := fun L =>
    sumTermsP env (dropZeros L) = sumTermsP env L) ?nil ?cons terms)
  · kan_rfl
  · kan_intro head
    kan_intro tail
    kan_intro ih
    kan_by_cases hv : (head.coeff == 0) = true
    · kan_exact ((congrArg (sumTermsP env) (if_pos hv)).trans
        (ih.trans ((Rat.zero_add (sumTermsP env tail)).symm.trans
          (congrArg (fun z => z + sumTermsP env tail)
            (mono_eval_of_coeff_zero env head (eq_of_beq hv)).symm))))
    · kan_exact ((congrArg (sumTermsP env) (if_neg hv)).trans
        (congrArg (fun x => head.eval env + x) ih))

/-- `collapseP` followed by `dropZeros` still preserves `sumTermsP`. -/
theorem dropZeros_collapseP_eval (env : Var → Rat) (terms : List Mono) :
    sumTermsP env (dropZeros (collapseP terms)) = sumTermsP env terms :=
  (dropZeros_eval env (collapseP terms)).trans (collapseP_eval env terms)

/-- Ghost-tolerant analogue of `eval_const_of_collapseP`: a polynomial whose collapsed terms
reduce (after dropping zero ghosts) to a single constant monomial evaluates to that constant. -/
theorem eval_const_of_dropZeros (env : Var → Rat) (p : MvPoly) (c : Rat)
    (h : dropZeros (collapseP p.terms) = [⟨c, []⟩]) : p.eval env = c :=
  ((dropZeros_collapseP_eval env p.terms).symm.trans (congrArg (sumTermsP env) h)).trans
    ((Rat.add_zero (c * 1)).trans (Rat.mul_one c))

/-- Ghost-tolerant refutation closer: a folded combination valued `0` whose collapse, after
dropping zero ghosts, is a single nonzero constant monomial, is a contradiction.  The
elaborator discharges `hc`/`h` with `mkDecideProof`. -/
theorem false_of_collapseP' (env : Var → Rat) (p : MvPoly) (c : Rat)
    (hzero : p.eval env = 0) (hc : ¬ (c = 0))
    (h : dropZeros (collapseP p.terms) = [⟨c, []⟩]) : False :=
  hc ((eval_const_of_dropZeros env p c h).symm.trans hzero)

/-! ## Equality-goal soundness (ideal membership)

Proving `a = b` is proving `a − b ∈ ⟨hyps⟩`: the goal polynomial `pa − pb`, minus the
cofactor combination `G = ∑ qᵢ·hypᵢ`, collapses to the empty term list (they are equal
polynomials), so `(pa − pb).eval = G.eval = 0`, hence `a = b`.  The two `Rat` helpers are
derived from the confirmed Mathlib-free surface (`Rat.sub_zero` / `eq_of_sub_eq_zero` are
not assumed). -/

/-- `-(0 : ℚ) = 0`, from `Rat.neg_add_cancel` + `Rat.add_zero`. -/
theorem negZeroR : (-(0 : Rat)) = 0 :=
  (Rat.add_zero (-(0 : Rat))).symm.trans (Rat.neg_add_cancel 0)

/-- `a - 0 = a` over ℚ. -/
theorem subZeroR (a : Rat) : a - 0 = a :=
  (Rat.sub_eq_add_neg a 0).trans ((congrArg (fun z => a + z) negZeroR).trans (Rat.add_zero a))

/-- `a - b = 0 → a = b` over ℚ, from `add`/`neg` cancellation. -/
theorem eqOfSubZeroR (a b : Rat) (h : a - b = 0) : a = b :=
  (Rat.add_zero a).symm.trans
    ((congrArg (fun z => a + z) (Rat.neg_add_cancel b).symm).trans
      ((Rat.add_assoc a (-b) b).symm.trans
        ((congrArg (fun z => z + b) (Rat.sub_eq_add_neg a b).symm).trans
          ((congrArg (fun z => z + b) h).trans (Rat.zero_add b)))))

/-- A polynomial whose terms collapse to the empty list evaluates to `0`. -/
theorem eval_zero_of_collapseP_nil (env : Var → Rat) (p : MvPoly)
    (h : collapseP p.terms = []) : p.eval env = 0 :=
  (collapseP_eval env p.terms).symm.trans (congrArg (sumTermsP env) h)

/-- Ghost-tolerant analogue: a polynomial whose collapsed terms reduce (after dropping zero
ghosts) to the empty list evaluates to `0`. -/
theorem eval_zero_of_dropZeros_nil (env : Var → Rat) (p : MvPoly)
    (h : dropZeros (collapseP p.terms) = []) : p.eval env = 0 :=
  (dropZeros_collapseP_eval env p.terms).symm.trans (congrArg (sumTermsP env) h)

/-- The equality-goal closer: given reifications `a = pa.eval env`, `b = pb.eval env`, a
cofactor combination `G` with `G.eval env = 0` (every hypothesis vanishes), and a proof
that `(pa − pb) − G` collapses away, conclude `a = b`.  The elaborator discharges `hnil`
with `mkDecideProof` and supplies `hG` from the folded cofactor combination. -/
theorem prove_eq (env : Var → Rat) (pa pb G : MvPoly) (a b : Rat)
    (pa_eq : a = pa.eval env) (pb_eq : b = pb.eval env) (hG : G.eval env = 0)
    (hnil : collapseP ((pa.sub pb).sub G).terms = []) : a = b :=
  let hD := eval_zero_of_collapseP_nil env ((pa.sub pb).sub G) hnil
  let hsz := (MvPoly.eval_sub env (pa.sub pb) G).symm.trans hD
  let hs0 := (subZeroR ((pa.sub pb).eval env)).symm.trans
    ((congrArg (fun z => (pa.sub pb).eval env - z) hG).symm.trans hsz)
  let hXY := (MvPoly.eval_sub env pa pb).symm.trans hs0
  pa_eq.trans ((eqOfSubZeroR (pa.eval env) (pb.eval env) hXY).trans pb_eq.symm)

/-- Ghost-tolerant equality-goal closer: as `prove_eq`, but `(pa − pb) − G` need only
collapse-and-drop-zeros to the empty list (the form that actually arises, since cofactor
multiplication leaves zero-coefficient ghosts).  The elaborator discharges `hnil` with
`mkDecideProof`. -/
theorem prove_eq' (env : Var → Rat) (pa pb G : MvPoly) (a b : Rat)
    (pa_eq : a = pa.eval env) (pb_eq : b = pb.eval env) (hG : G.eval env = 0)
    (hnil : dropZeros (collapseP ((pa.sub pb).sub G).terms) = []) : a = b :=
  let hD := eval_zero_of_dropZeros_nil env ((pa.sub pb).sub G) hnil
  let hsz := (MvPoly.eval_sub env (pa.sub pb) G).symm.trans hD
  let hs0 := (subZeroR ((pa.sub pb).eval env)).symm.trans
    ((congrArg (fun z => (pa.sub pb).eval env - z) hG).symm.trans hsz)
  let hXY := (MvPoly.eval_sub env pa pb).symm.trans hs0
  pa_eq.trans ((eqOfSubZeroR (pa.eval env) (pb.eval env) hXY).trans pb_eq.symm)

end KanSaturation
