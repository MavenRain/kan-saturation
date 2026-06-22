import KanSaturation.Core.Constraint
import KanSaturation.Core.Saturation
import KanTactics

/-!
# `KanSaturation.Core.Eliminate`

The linear legs' control structure: **Fourier–Motzkin variable elimination**.  Where the
ideal leg accumulates (Buchberger never drops a fact, so it is bounded by a capacity
measure), the linear legs *eliminate one variable per round and drop every constraint
mentioning it*, so the genuine well-founded measure is the **number of variables still to
eliminate**, which the recursion strictly decreases by construction.

This module is generic over the fact type `F`: an instance supplies `eliminate v facts`
(combine and drop on `v`) and a fact-level `refuted?`, and gets a `Saturation` instance via
`ElimState`.  The single elimination loop and its termination proof live here once; the
integer and ordered-field legs differ only in their `eliminate` (the integer leg adds
integrality tightening, the ordered-field leg does not).  Mathlib-free; the measure-decrease
proof is kan-tactics only.
-/

namespace KanSaturation

/-- The Fourier–Motzkin state the engine iterates: the working constraints `facts` and the
schedule `todo` of variables still to eliminate.  The engine basis is a singleton holding
one such state; each round eliminates `todo`'s head and shrinks the schedule, so the
schedule length *is* the strictly-decreasing variable-count measure. -/
structure ElimState (F : Type) where
  /-- The current working constraints. -/
  facts : Array F
  /-- The remaining variable-elimination schedule. -/
  todo  : List Var

/-- The variable-count measure: the head state's remaining schedule length. -/
def elimMeasure {F : Type} (basis : Array (ElimState F)) : Nat :=
  (basis.toList.head?).elim 0 (fun s => s.todo.length)

/-- Refutation check, delegated to the fact-level `factRefuted?` on the head state. -/
def elimRefuted? {F Cert : Type} (factRefuted? : Array F → Option Cert)
    (basis : Array (ElimState F)) : Option Cert :=
  (basis.toList.head?).bind (fun s => factRefuted? s.facts)

/-- One elimination round: eliminate the head scheduled variable from the working
constraints and drop it from the schedule, carrying the proof that the variable count
strictly decreased.  `none` once the schedule is empty (a fixpoint: only constant
constraints remain, already checked by `elimRefuted?`). -/
def elimRound {F : Type} (eliminate : Var → Array F → Array F)
    (basis : Array (ElimState F)) :
    Option { basis' : Array (ElimState F) // elimMeasure basis' < elimMeasure basis } :=
  match h : basis.toList with
  | [] => none
  | _ :: _ :: _ => none
  | [s] =>
      match hs : s.todo with
      | [] => none
      | v :: rest =>
          some ⟨#[{ facts := eliminate v s.facts, todo := rest }], by
            kan_exact (Nat.lt_of_lt_of_eq (Nat.lt_succ_self rest.length)
              (((congrArg (fun l => (List.head? l).elim 0 (fun s : ElimState F => s.todo.length)) h :
                  elimMeasure basis = s.todo.length).trans
                (congrArg (fun t => List.length t) hs)).symm) :
              elimMeasure #[{ facts := eliminate v s.facts, todo := rest }] < elimMeasure basis)⟩

end KanSaturation
