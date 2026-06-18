import KanSaturation.Core.PolyReflect
import KanSaturation.Instances.Ideal
import KanSaturation.Tactic.Reify
import KanSaturation.Tactic.SaturateField
import KanTactics
import Lean

/-!
# `KanSaturation.Tactic.SaturateIdeal`

The ideal/`polyrith` leg of the tactic layer: a verified **polynomial** reifier for `ℚ`
expressions, and the replay that turns an `Ideal.solve` Nullstellensatz refutation (a
nonzero constant in `⟨hyps⟩`) or an `Ideal.member?` ideal-membership certificate into a
kernel-checked proof — of `False` from contradictory `ℚ` equalities, or of a `ℚ` equality
goal that lies in the ideal of the equality hypotheses.

Mirrors the ordered-field reifier/replay (`Tactic.SaturateField`), but over the
multivariate polynomial substrate (`Core.PolyReflect`) rather than linear forms, and with
no linearity restriction on products: a multiplication recurses into *both* factors
(`reifyP_mul`), so genuinely nonlinear hypotheses such as `x * x = 2` are reified exactly.

Scope (this first cut): `+`, `-`, unary `-`, `*` (general products), and `ℚ` integer
literals are reified structurally; **`^` (`HPow`) and `/` (`HDiv`) are deliberately
atomized** — interned as opaque atoms via `internAtom`, which is always sound (the atom
denotes whatever the subterm denotes), at the cost of not seeing through them.  Reusing
those atoms keeps the goal poly and hypothesis polys on the same atom indices, which is
what makes `Ideal.member?` cofactor recovery line up.

This is meta-programming on `Expr` (exempt from the kan-tactics-only rule), Mathlib-free,
and total/`Option`-returning, with the single boundary `throwError` living in the shared
`kan_saturate` elaborator.
-/

open Lean Lean.Meta Lean.Elab.Tactic

namespace KanSaturation

deriving instance ToExpr for Mono
deriving instance ToExpr for MvPoly

namespace Tactic

/-! ## Verified polynomial reification -/

/-- Verified polynomial reification at `ℚ`: returns `(p, pExpr, proof : e = pExpr.eval env)`,
interning atoms.  `pExpr` is the `Expr` the proof actually mentions — for a compound shape
it is the *unreduced* `MvPoly.add`/`.sub`/`.neg`/`.mul` application of the children's poly
Exprs (NOT `toExpr p`, which `toExpr` would evaluate to a syntactically different normal
form, breaking the parent `mkAppM`'s type check).  `p` is the corresponding evaluated
`MvPoly` value (defeq to `pExpr`) for the downstream engine calls.

Handles `+`, `-`, unary `-`, general `*` (recursing into both factors), and `ℚ` integer
literals; any other shape (`^`, `/`, a variable, an opaque term) is interned as an opaque
atom, which is always sound.  Mirrors `reifyEvalProofQ`'s StateT-atom mechanics. -/
partial def reifyPolyProof (envExpr : Expr) (e : Expr) :
    StateT (Array Expr) MetaM (MvPoly × Expr × Expr) := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => do
      let (pa, paE, ea) ← reifyPolyProof envExpr a
      let (pb, pbE, eb) ← reifyPolyProof envExpr b
      let pE ← mkAppM ``MvPoly.add #[paE, pbE]
      let pf ← mkAppM ``reifyP_add #[envExpr, paE, pbE, a, b, ea, eb]
      pure (pa.add pb, pE, pf)
  | (``HSub.hSub, #[_, _, _, _, a, b]) => do
      let (pa, paE, ea) ← reifyPolyProof envExpr a
      let (pb, pbE, eb) ← reifyPolyProof envExpr b
      let pE ← mkAppM ``MvPoly.sub #[paE, pbE]
      let pf ← mkAppM ``reifyP_sub #[envExpr, paE, pbE, a, b, ea, eb]
      pure (pa.sub pb, pE, pf)
  | (``Neg.neg, #[_, _, a]) => do
      let (pa, paE, ea) ← reifyPolyProof envExpr a
      let pE ← mkAppM ``MvPoly.neg #[paE]
      let pf ← mkAppM ``reifyP_neg #[envExpr, paE, a, ea]
      pure (pa.neg, pE, pf)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => do
      let (pa, paE, ea) ← reifyPolyProof envExpr a
      let (pb, pbE, eb) ← reifyPolyProof envExpr b
      let pE ← mkAppM ``MvPoly.mul #[paE, pbE]
      let pf ← mkAppM ``reifyP_mul #[envExpr, paE, pbE, a, b, ea, eb]
      pure (pa.mul pb, pE, pf)
  | _ => do
      match ← ratIntLit? e with
      | some (k, litEq) => do
          -- `litEq : e = ((k:Int):ℚ)`; `reifyP_const env c : c = (MvPoly.const c).eval env`
          -- with `c := ((k:Int):ℚ)`.  The embedded coefficient value and the bridge's RHS
          -- agree because `mkAppM` unifies `reifyP_const`'s `c` against the cast literal.
          let c : Rat := (k : Rat)
          let cE := toExpr c
          let pE ← mkAppM ``MvPoly.const #[cE]
          let constPf ← mkAppM ``reifyP_const #[envExpr, cE]
          let pf ← mkEqTrans litEq constPf
          pure (MvPoly.const c, pE, pf)
      | none => reifyAtomP envExpr e
where
  /-- Intern `e` as an atom: `env v = (MvPoly.atom v).eval env` (`env v` reduces to `e`). -/
  reifyAtomP (envExpr : Expr) (e : Expr) : StateT (Array Expr) MetaM (MvPoly × Expr × Expr) := do
    let v ← internAtom e
    let vE := toExpr v
    let pE ← mkAppM ``MvPoly.atom #[vE]
    let pf ← mkAppM ``reifyP_atom #[envExpr, vE]
    pure (MvPoly.atom v, pE, pf)

/-- Intern the atoms of `e` (mirroring `reifyPolyProof`'s recursion exactly, so indices
agree) without building any proof — the env-independent first pass. -/
partial def discoverAtomsP (e : Expr) : StateT (Array Expr) MetaM Unit := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => discoverAtomsP a; discoverAtomsP b
  | (``HSub.hSub, #[_, _, _, _, a, b]) => discoverAtomsP a; discoverAtomsP b
  | (``Neg.neg, #[_, _, a]) => discoverAtomsP a
  | (``HMul.hMul, #[_, _, _, _, a, b]) => discoverAtomsP a; discoverAtomsP b
  | _ => do
      match ← ratIntLit? e with
      | some _ => pure ()
      | none => discard (internAtom e)

/-! ## Equality-hypothesis collection and cofactor folding -/

/-- Collect the local `ℚ` equality hypotheses as `(a, b, proof)` with `proof : a = b`. -/
def collectEqHyps : MetaM (Array (Expr × Expr × Expr)) := do
  (← getLCtx).foldlM (init := (#[] : Array (Expr × Expr × Expr))) fun acc decl => do
    if decl.isImplementationDetail then return acc
    match decl.type.getAppFnArgs with
    | (``Eq, #[ty, a, b]) =>
        if ty.isConstOf ``Rat then return acc.push (a, b, decl.toExpr) else return acc
    | _ => return acc

/-- `MvPoly.eval env pExpr` as an `Expr`, for a poly already given as an `Expr` (kept
unreduced so it matches the proof terms that mention the same `pExpr`). -/
def mkEvalExpr (envExpr pExpr : Expr) : MetaM Expr :=
  mkAppM ``MvPoly.eval #[envExpr, pExpr]

/-- Fold a resolved cofactor `combo` into the combination polynomial `G = ∑ qᵢ · pᵢ`,
returning `(Gvalue, Gexpr, proof : Gexpr.eval env = 0)`.  `facts.[i] = (pᵢ, pᵢExpr, holdsᵢ)`
with `holdsᵢ : pᵢExpr.eval env = 0`; `Gexpr` is the *unreduced* `MvPoly.add`/`.mul`
application the proof mentions (so the closers can reuse it verbatim).  Cofactors `qᵢ`
come from the certificate as fresh values, so `toExpr qᵢ` is fine.  Returns `none` on a
stale generator index. -/
def foldCombo (envExpr : Expr) (combo : List (MvPoly × Nat))
    (facts : Array (MvPoly × Expr × Expr)) : MetaM (Option (MvPoly × Expr × Expr)) := do
  let zeroProof ← mkAppM ``MvPoly.eval_zero #[envExpr]
  let init : Option (MvPoly × Expr × Expr) :=
    some (MvPoly.zero, toExpr MvPoly.zero, zeroProof)
  combo.foldlM (init := init) fun acc entry => do
    match acc with
    | none => pure none
    | some (accPoly, accExpr, accProof) =>
        let (q, i) := entry
        match facts[i]? with
        | none => pure none
        | some (pI, pIExpr, holdsI) => do
            -- term `q · pᵢ` vanishes: `(q.mul pᵢ).eval = q.eval * pᵢ.eval = q.eval * 0 = 0`
            let qExpr := toExpr q
            let termExpr ← mkAppM ``MvPoly.mul #[qExpr, pIExpr]
            let qEval ← mkEvalExpr envExpr qExpr
            let pEval ← mkEvalExpr envExpr pIExpr
            let mulZero ← mkAppM ``holdsP_mul_zero #[qEval, pEval, holdsI]
            let termProof ← mkEqTrans (← mkAppM ``MvPoly.eval_mul #[envExpr, qExpr, pIExpr])
              mulZero
            -- accumulate: `(acc + term).eval = acc.eval + term.eval = 0 + 0 = 0`
            let newExpr ← mkAppM ``MvPoly.add #[accExpr, termExpr]
            let accEval ← mkEvalExpr envExpr accExpr
            let termEval ← mkEvalExpr envExpr termExpr
            let addZero ← mkAppM ``holdsP_add_zero #[accEval, termEval, accProof, termProof]
            let newProof ← mkEqTrans
              (← mkAppM ``MvPoly.eval_add #[envExpr, accExpr, termExpr]) addZero
            pure (some (accPoly.add (q.mul pI), newExpr, newProof))

/-! ## The refutation and equality-goal replays -/

/-- Run the ideal engine on the current `ℚ` equality hypotheses and replay its
Nullstellensatz certificate (a nonzero constant in the ideal) into a kernel-checked proof
of `False`.  Returns `none` when there is no refutation, a combination references a stale
index, or the folded combination does not collapse to a single nonzero constant monomial
(all handled as data, never thrown). -/
def proveFalseP : MetaM (Option Expr) := do
  let hyps ← collectEqHyps
  -- pass 1: discover atoms across every equality side, so indices align
  let atoms ← hyps.foldlM (init := (#[] : Array Expr)) fun atoms hyp => do
    let (a, b, _) := hyp
    let (_, atoms) ← (do discoverAtomsP a; discoverAtomsP b).run atoms
    pure atoms
  let envExpr ← buildEnvQ atoms
  -- pass 2: reify each equality into its difference poly with `holds : pᵢExpr.eval env = 0`
  let result ← hyps.foldlM
    (init := ((#[], atoms) : Array (MvPoly × Expr × Expr) × Array Expr))
    fun acc hyp => do
      let (facts, atoms') := acc
      let (a, b, hyp) := hyp
      let ((pa, paE, ea), atoms'') ← (reifyPolyProof envExpr a).run atoms'
      let ((pb, pbE, eb), atoms''') ← (reifyPolyProof envExpr b).run atoms''
      let factPoly := pa.sub pb
      let factExpr ← mkAppM ``MvPoly.sub #[paE, pbE]
      let pp ← mkAppM ``reifyP_sub #[envExpr, paE, pbE, a, b, ea, eb]
      let holds ← mkAppM ``holdsP_of_eq #[factExpr, envExpr, a, b, pp, hyp]
      pure (facts.push (factPoly, factExpr, holds), atoms''')
  let facts := result.1
  let factPolys := (facts.map (·.1)).toList
  -- resolve the certificate, then fold its cofactor combo into `(G, gExpr, gProof)`
  match (Ideal.solve factPolys).toOption with
  | none => pure none
  | some cert => do
      match ← foldCombo envExpr cert.combo facts with
      | none => pure none
      | some (gPoly, gExpr, gProof) =>
          -- after dropping zero-coefficient ghosts, `G` must reduce to a single nonzero
          -- constant monomial `⟨c, []⟩`
          match dropZeros (collapseP gPoly.terms) with
          | [⟨c, []⟩] =>
              if c == 0 then pure none
              else do
                let hc ← mkDecideProof (← mkAppM ``Ne #[toExpr c, toExpr (0 : Rat)])
                let collapseExpr ← mkAppM ``dropZeros
                  #[← mkAppM ``collapseP #[← mkAppM ``MvPoly.terms #[gExpr]]]
                let h ← mkDecideProof
                  (← mkEq collapseExpr (toExpr ([(⟨c, []⟩ : Mono)] : List Mono)))
                pure (some (← mkAppM ``false_of_collapseP'
                  #[envExpr, gExpr, toExpr c, gProof, hc, h]))
          | _ => pure none

/-- Prove a `ℚ` equality goal `a = b` by ideal membership: reify the goal and the equality
hypotheses against a *shared* atom environment, run `Ideal.member?` on `pa − pb`, and replay
the cofactor representation `(pa − pb) = ∑ qᵢ · hypᵢ` into a kernel-checked proof.  Returns
`none` when the goal does not lie in the ideal of the hypotheses (or a stale index appears). -/
def dispatchGoalP (goalType : Expr) : MetaM (Option Expr) := do
  match goalType.getAppFnArgs with
  | (``Eq, #[ty, a, b]) =>
      if ty.isConstOf ``Rat then do
        let hyps ← collectEqHyps
        -- pass 1: ONE shared discovery over the goal sides AND every hyp side, so the goal
        -- poly and the hyp polys share atom indices (essential for `member?`).
        let atoms0 ← (do discoverAtomsP a; discoverAtomsP b).run #[]
        let atoms ← hyps.foldlM (init := atoms0.2) fun atoms hyp => do
          let (ha, hb, _) := hyp
          let (_, atoms') ← (do discoverAtomsP ha; discoverAtomsP hb).run atoms
          pure atoms'
        let envExpr ← buildEnvQ atoms
        -- reify the goal sides
        let ((pa, paE, ea), atoms) ← (reifyPolyProof envExpr a).run atoms
        let ((pb, pbE, eb), atoms) ← (reifyPolyProof envExpr b).run atoms
        -- reify the hyps into difference polys + their `holds` proofs
        let result ← hyps.foldlM
          (init := ((#[], atoms) : Array (MvPoly × Expr × Expr) × Array Expr))
          fun acc hyp => do
            let (facts, atoms') := acc
            let (ha, hb, hyp) := hyp
            let ((pha, phaE, eha), atoms'') ← (reifyPolyProof envExpr ha).run atoms'
            let ((phb, phbE, ehb), atoms''') ← (reifyPolyProof envExpr hb).run atoms''
            let factPoly := pha.sub phb
            let factExpr ← mkAppM ``MvPoly.sub #[phaE, phbE]
            let pp ← mkAppM ``reifyP_sub #[envExpr, phaE, phbE, ha, hb, eha, ehb]
            let holds ← mkAppM ``holdsP_of_eq #[factExpr, envExpr, ha, hb, pp, hyp]
            pure (facts.push (factPoly, factExpr, holds), atoms''')
        let facts := result.1
        let factPolys := (facts.map (·.1)).toList
        match Ideal.member? factPolys (pa.sub pb) with
        | none => pure none
        | some combo => do
            match ← foldCombo envExpr combo facts with
            | none => pure none
            | some (_, gExpr, gProof) => do
                let goalDiffExpr ← mkAppM ``MvPoly.sub #[paE, pbE]
                let collapseExpr ← mkAppM ``dropZeros #[← mkAppM ``collapseP
                  #[← mkAppM ``MvPoly.terms #[← mkAppM ``MvPoly.sub #[goalDiffExpr, gExpr]]]]
                let hnil ← mkDecideProof (← mkEq collapseExpr (toExpr ([] : List Mono)))
                pure (some (← mkAppM ``prove_eq'
                  #[envExpr, paE, pbE, gExpr, a, b, ea, eb, gProof, hnil]))
      else pure none
  | _ => pure none

end Tactic
end KanSaturation
