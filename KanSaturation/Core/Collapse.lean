import KanSaturation.Core.Constraint
import KanSaturation.Core.Eval
import KanTactics

/-!
# `KanSaturation.Core.Collapse`

Term collection for the certificate replay: merging like terms and discharging an
all-zero-coefficient term list.  Together these let the replay prove that a folded
combination whose variable coefficients cancel evaluates to its constant.  Proven
with kan-tactics only, in the `Core.Eval` style.
-/

namespace KanSaturation

/-- Insert a term into a list, summing coefficients when the variable already occurs. -/
def insertTerm : (Int × Var) → List (Int × Var) → List (Int × Var)
  | (c, v), [] => [(c, v)]
  | (c, v), (c', v') :: rest =>
      if v == v' then (c + c', v') :: rest else (c', v') :: insertTerm (c, v) rest

/-- Collapse like terms by repeated insertion. -/
def collapse (terms : List (Int × Var)) : List (Int × Var) :=
  terms.foldr insertTerm []

/-- Inserting a term shifts `sumTerms` by that term's contribution. -/
theorem insert_eval (env : Var → Int) (t : Int × Var) (l : List (Int × Var)) :
    sumTerms env (insertTerm t l) = t.1 * env t.2 + sumTerms env l := by
  kan_refine (List.rec (motive := fun L =>
    sumTerms env (insertTerm t L) = t.1 * env t.2 + sumTerms env L) ?nil ?cons l)
  · kan_rfl
  · kan_intro head
    kan_intro tail
    kan_intro ih
    kan_by_cases hv : (t.2 == head.2) = true
    · kan_exact ((congrArg (sumTerms env) (if_pos hv)).trans
        ((congrArg (fun x => x + sumTerms env tail) (Int.add_mul t.1 head.1 (env head.2))).trans
          ((Int.add_assoc (t.1 * env head.2) (head.1 * env head.2) (sumTerms env tail)).trans
            (congrArg (fun w => t.1 * env w + (head.1 * env head.2 + sumTerms env tail))
              (eq_of_beq hv).symm))))
    · kan_exact ((congrArg (sumTerms env) (if_neg hv)).trans
        ((congrArg (fun x => head.1 * env head.2 + x) ih).trans
          (Int.add_left_comm (head.1 * env head.2) (t.1 * env t.2) (sumTerms env tail))))

/-- Collapsing preserves `sumTerms`. -/
theorem collapse_eval (env : Var → Int) (terms : List (Int × Var)) :
    sumTerms env (collapse terms) = sumTerms env terms := by
  kan_refine (List.rec (motive := fun L =>
    sumTerms env (collapse L) = sumTerms env L) ?nil ?cons terms)
  · kan_rfl
  · kan_intro head
    kan_intro tail
    kan_intro ih
    kan_exact ((insert_eval env head (collapse tail)).trans
      (congrArg (fun x => head.1 * env head.2 + x) ih))

/-- Predicate: a term has zero coefficient. -/
def isZeroCoeff (t : Int × Var) : Bool := t.1 == 0

/-- An all-zero-coefficient term list sums to `0`. -/
theorem sumTerms_allZero (env : Var → Int) (terms : List (Int × Var)) :
    terms.all isZeroCoeff = true → sumTerms env terms = 0 := by
  kan_refine (List.rec (motive := fun L =>
    L.all isZeroCoeff = true → sumTerms env L = 0) ?nil ?cons terms)
  · kan_intro h0
    kan_rfl
  · kan_intro head
    kan_intro tail
    kan_intro ih
    kan_intro hcons
    kan_exact ((congrArg (fun c => c * env head.2 + sumTerms env tail)
        (eq_of_beq (Bool.and_eq_true_iff.mp hcons).1)).trans
      ((congrArg (fun x => x + sumTerms env tail) (Int.zero_mul (env head.2))).trans
        ((Int.zero_add (sumTerms env tail)).trans (ih (Bool.and_eq_true_iff.mp hcons).2))))

end KanSaturation
