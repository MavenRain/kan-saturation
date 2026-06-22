/-!
# `KanSaturation.Core.Saturation`

The interface encoding the *unifying completeness theorem* as exactly the data one
engine needs.  Each of `omega`, `linarith`, `polyrith` is recovered by supplying a
`Saturation` instance; the shared `Engine` then runs the single saturate-then-reduce
algorithm against it.

`Cert` is an `outParam`: an instance fixes both the fact type `F` and the shape of
the refutation certificate it emits (later replayed into a kernel-checked proof by
the tactic layer).  Soundness of the resulting tactic rests on that replay, not on
the (separately stated) tightness theorem (see `KanSaturation.Reflector`).

## One engine, one well-founded measure

The procedure is abstract completion: *superpose, simplify, delete redundant*, until a
contradiction surfaces or a fixpoint is reached.  An instance presents this as a single
**`round`**, returning the next basis packaged with a proof that a per-instance
**`measure`** strictly decreased.  The shared `Engine.saturate` is therefore one well-founded loop
(`termination_by measure`), not a fuel cutoff: the linear legs supply the genuine
variable-count measure (Fourier–Motzkin eliminates one variable per round and drops the
constraints mentioning it), while the ideal leg supplies the bounded accumulate measure
(`Engine.accumulateRound`) that reproduces the Buchberger closure.
-/

namespace KanSaturation

/-- A structure-specific saturation, presented as the data the single engine consumes.
The three instances recover the three deciders by supplying:

* `refuted?`: detection of the contradiction witness (`-1` in the closure, `0 < 0`,
  a nonzero constant in the ideal), returning a replayable certificate;
* `measure`: a well-founded measure on the *basis*, strictly decreased by every
  productive `round` (the variable count for the linear legs, the bounded remaining
  capacity for the ideal leg);
* `round`: one saturation round (superpose, simplify, and delete-redundant fused),
  returning the next basis paired with the proof that `measure` strictly dropped, or
  `none` at a fixpoint. -/
class Saturation (F : Type) (Cert : outParam Type) where
  /-- A refutation certificate, if the basis already exhibits the contradiction. -/
  refuted? : Array F → Option Cert
  /-- A well-founded measure on the basis, strictly decreased by every productive round. -/
  measure  : Array F → Nat
  /-- One saturation round: the next basis with a proof its measure strictly dropped, or
  `none` at a fixpoint. -/
  round    : (basis : Array F) → Option { basis' : Array F // measure basis' < measure basis }

end KanSaturation
