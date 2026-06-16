/-!
# `KanSaturation.Core.Saturation`

The interface encoding the *unifying completeness theorem* as exactly the data one
engine needs.  Each of `omega`, `linarith`, `polyrith` is recovered by supplying a
`Saturation` instance; the shared `Engine` then runs the single saturate-then-reduce
algorithm against it.

`Cert` is an `outParam`: an instance fixes both the fact type `F` and the shape of
the refutation certificate it emits (later replayed into a kernel-checked proof by
the tactic layer).  Soundness of the resulting tactic rests on that replay, not on
the (separately stated) tightness theorem — see `KanSaturation.Reflector`.
-/

namespace KanSaturation

/-- A structure-specific saturation, presented as the data the single engine
consumes.  The three instances recover the three deciders by supplying:

* `consequences` — the saturation step: integer tightening (`omega`), bound
  combination (`linarith`), or S-polynomial superposition (`polyrith`);
* `measure`     — a well-founded bound witnessing that the step makes progress;
* `reduce`      — normal-form reduction of a fact modulo the current basis;
* `refuted?`    — detection of the contradiction witness (`-1` in the closure,
  `0 < 0`, an empty residue), returning a replayable certificate. -/
class Saturation (F : Type) (Cert : outParam Type) where
  /-- Consequences of `f` against the current basis (the saturation step). -/
  consequences : Array F → F → Array F
  /-- A well-founded measure bounding the saturation step. -/
  measure : F → Nat
  /-- Normal-form reduction of `f` modulo the basis. -/
  reduce : Array F → F → F
  /-- A refutation certificate, if the basis already exhibits the contradiction. -/
  refuted? : Array F → Option Cert

end KanSaturation
