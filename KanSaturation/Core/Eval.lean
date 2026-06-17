import KanSaturation.Core.Constraint
import KanTactics

/-!
# `KanSaturation.Core.Eval`

Denotation of a `LinForm` under an environment, and the normalization-soundness
lemmas the certificate replay reflects through.  Per the project convention these
lemmas are proven with **kan-tactics only** (no `simp`/`ring`/`omega`): they are the
irreducible arithmetic bootstrap that `kan_saturate` itself cannot discharge.

Note on technique: `kan_induction` cannot infer the motive for these goals, so the
recursor is applied explicitly via `kan_refine (List.rec (motive := …) …)`, and each
case is closed by `kan_exact` of an explicit proof term (the constructor reductions
of `sumTerms`/`++` hold definitionally, so no `dsimp` is needed — and `kan_dsimp`
would over-reduce `Int` into `Int.rec`).
-/

namespace KanSaturation

/-- Evaluate the linear part of a form under an environment, by structural recursion
on the term list. -/
def sumTerms (env : Var → Int) : List (Int × Var) → Int
  | []             => 0
  | (c, v) :: rest => c * env v + sumTerms env rest

/-- Evaluate a linear form under an environment. -/
def LinForm.eval (env : Var → Int) (f : LinForm) : Int :=
  sumTerms env f.terms + f.const

/-- `sumTerms` is additive over list append (the keystone induction). -/
theorem sumTerms_append (env : Var → Int) (l1 l2 : List (Int × Var)) :
    sumTerms env (l1 ++ l2) = sumTerms env l1 + sumTerms env l2 := by
  kan_refine (List.rec (motive := fun L =>
    sumTerms env (L ++ l2) = sumTerms env L + sumTerms env l2) ?nil ?cons l1)
  · kan_exact (Int.zero_add (sumTerms env l2)).symm
  · kan_intro head
    kan_intro tail
    kan_intro ih
    kan_exact ((congrArg (fun x => head.1 * env head.2 + x) ih).trans
      (Int.add_assoc (head.1 * env head.2) (sumTerms env tail) (sumTerms env l2)).symm)

/-- `eval` is additive over `LinForm.add`.  (The term is the explicit reassociation
`(Sf + Sg) + (cf + cg) = (Sf + cf) + (Sg + cg)` after `sumTerms_append`.) -/
theorem LinForm.eval_add (env : Var → Int) (f g : LinForm) :
    (f.add g).eval env = f.eval env + g.eval env := by
  kan_exact ((congrArg (fun x => x + (f.const + g.const))
      (sumTerms_append env f.terms g.terms)).trans
    (((Int.add_assoc (sumTerms env f.terms) (sumTerms env g.terms) (f.const + g.const)).trans
        (congrArg (fun x => sumTerms env f.terms + x)
          (((Int.add_assoc (sumTerms env g.terms) f.const g.const).symm).trans
            ((congrArg (fun y => y + g.const) (Int.add_comm (sumTerms env g.terms) f.const)).trans
              (Int.add_assoc f.const (sumTerms env g.terms) g.const))))).trans
      (Int.add_assoc (sumTerms env f.terms) f.const (sumTerms env g.terms + g.const)).symm))

/-- `sumTerms` commutes with scaling all coefficients. -/
theorem sumTerms_scale (env : Var → Int) (k : Int) (l : List (Int × Var)) :
    sumTerms env (l.map (fun t => (k * t.1, t.2))) = k * sumTerms env l := by
  kan_refine (List.rec (motive := fun L =>
    sumTerms env (L.map (fun t => (k * t.1, t.2))) = k * sumTerms env L) ?nil ?cons l)
  · kan_exact (Int.mul_zero k).symm
  · kan_intro head
    kan_intro tail
    kan_intro ih
    kan_exact ((congrArg (fun x => (k * head.1) * env head.2 + x) ih).trans
      ((congrArg (fun y => y + k * sumTerms env tail) (Int.mul_assoc k head.1 (env head.2))).trans
        (Int.mul_add k (head.1 * env head.2) (sumTerms env tail)).symm))

/-- `eval` commutes with `LinForm.scale`. -/
theorem LinForm.eval_scale (env : Var → Int) (k : Int) (f : LinForm) :
    (f.scale k).eval env = k * f.eval env := by
  kan_exact ((congrArg (fun x => x + k * f.const) (sumTerms_scale env k f.terms)).trans
    (Int.mul_add k (sumTerms env f.terms) f.const).symm)

/-- A constant form evaluates to its constant. -/
theorem LinForm.eval_const (env : Var → Int) (c : Int) :
    (LinForm.mk [] c).eval env = c :=
  Int.zero_add c

/-- A single-variable unit form evaluates to that variable's value. -/
theorem LinForm.eval_atom (env : Var → Int) (v : Var) :
    (LinForm.mk [(1, v)] 0).eval env = env v :=
  ((Int.add_zero (1 * env v + 0)).trans (Int.add_zero (1 * env v))).trans (Int.one_mul (env v))

end KanSaturation
