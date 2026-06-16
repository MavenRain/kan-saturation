import KanSaturation.Core.Constraint
import KanSaturation.Core.Eval
import KanTactics

/-!
# `KanSaturation.Core.Reflect`

The semantic side of the certificate replay: when a `Fact` *holds* under an
environment, and the soundness building blocks the replay folds the certificate
through.  All proofs are kan-tactics only, building on `Core.Eval`'s lemmas.
-/

namespace KanSaturation

/-- A fact holds under `env` when its form satisfies the asserted relation with `0`. -/
def Fact.holds (env : Var → Int) (fact : Fact) : Prop :=
  match fact.rel with
  | .eq => fact.form.eval env = 0
  | .le => 0 ≤ fact.form.eval env
  | .lt => 0 < fact.form.eval env

/-- Scaling a `≤`-form by a nonnegative coefficient preserves `0 ≤ eval`. -/
theorem holds_le_scale (env : Var → Int) (k : Int) (f : LinForm)
    (hk : 0 ≤ k) (hf : 0 ≤ f.eval env) : 0 ≤ (f.scale k).eval env := by
  kan_exact ((LinForm.eval_scale env k f).symm ▸ Int.mul_nonneg hk hf)

/-- Adding two `≤`-forms preserves `0 ≤ eval`. -/
theorem holds_le_add (env : Var → Int) (f g : LinForm)
    (hf : 0 ≤ f.eval env) (hg : 0 ≤ g.eval env) : 0 ≤ (f.add g).eval env := by
  kan_exact ((LinForm.eval_add env f g).symm ▸ Int.add_nonneg hf hg)

/-- A constant `≤`-residual that holds bounds its constant below by `0`. -/
theorem le_const_of_holds (env : Var → Int) (c : Int)
    (h : 0 ≤ (LinForm.mk [] c).eval env) : 0 ≤ c := by
  kan_exact (Int.zero_add c ▸ h)

end KanSaturation
