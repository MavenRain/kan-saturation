import KanTactics

/-!
# `KanSaturation.Reflector`

The categorical capstone the thesis names: the **saturation Kan extension**.

The three deciders (`Instances.{Integer,OrderedField,Ideal}`) recover `omega`,
`linarith`, `polyrith` as instances of one saturate-then-reduce engine, each
sound by a per-call kernel-checked certificate.  This module is the *other* half
of the thesis: the categorical statement of what saturation **is**.

## The construction

Under the *unifying-completeness (tightness) theorem* the saturation map is a
**closure operator** `cl` on the entailment preorder of configurations:

* `infl` (inflationary): saturation only adds consequences (`x ≤ cl x`);
* `mono` (monotone): it respects entailment (`x ≤ y → cl x ≤ cl y`);
* `idem` (idempotent): it terminates at a fixed point (`cl (cl x) = cl x`).

A preorder is a **thin category** (at most one morphism between objects), so every
categorical coherence law below (associativity, unit laws, functoriality,
naturality, the triangle identities) is discharged by *thinness* alone
(`plift_subsingleton`).  The only real content is the three closure laws.

The fixed points form the **reflective subcategory** of saturated configurations.
Saturation, corestricted to that subcategory, is **left adjoint** to the inclusion
(`reflection : Adjunction saturate include'`).  Feeding that adjunction to
`comp-cat-theory`'s `adjToLan` realizes the inclusion as a **left Kan extension**

  `include' = Lan_saturate (Id)`          (`lan`)

and dually `adjToRan` realizes saturation itself as a **right Kan extension**

  `saturate = Ran_include' (Id)`          (`ran`)

This is "all concepts are Kan extensions" (Mac Lane), here for the saturation reflector.

## Soundness boundary

This module assumes the three closure laws *as data* (`class Closure`).
Discharging them for a concrete engine **is** that engine's tightness theorem
(Presburger / Farkas / Nullstellensatz), which the library states per instance and
never makes load-bearing: `kan_saturate`'s soundness rests on the certificate
replay, not on this construction.  So nothing here is imported by the tactic legs;
it is the conceptual capstone, kept axiom-clean (`Example.satToTop` witnesses the
whole pipeline with `#print axioms` showing only the standard three).

All proofs are **kan-tactics only**, per the library conventions.
-/

open CompCatTheory
open Category Functor NatTrans

namespace KanSaturation

universe u

namespace Reflector

/-! ## Thinness

Any two morphisms of a preorder-as-category are equal, because `Hom x y` is
`PLift` of a proposition and `PLift` of a proposition is a subsingleton.  This
single lemma closes *every* equational obligation in the construction. -/

/-- A `PLift` of a proposition is a subsingleton: the morphisms of a thin category
are unique.  Closes all the categorical coherence laws below. -/
theorem plift_subsingleton {p : Prop} (f g : PLift p) : f = g := by
  kan_exact (Subsingleton.elim f g)

/-! ## Preorders as thin categories -/

/-- A preorder: the exact data a thin category needs.  A class, so the induced thin
`Category` instance is found by the `⋙`/`idFunctor` machinery `adjToLan` runs on. -/
class Preorder (α : Type u) where
  /-- The entailment order. -/
  le : α → α → Prop
  /-- Reflexivity. -/
  le_refl : (x : α) → le x x
  /-- Transitivity. -/
  le_trans : {x y z : α} → le x y → le y z → le x z

/-- A preorder is a thin category: a (unique) morphism `x ⟶ y` exactly when `x ≤ y`.
All three category laws hold by thinness. -/
instance Preorder.toCat (α : Type u) [Preorder α] : Category α where
  Hom x y := PLift (Preorder.le x y)
  id x := ⟨Preorder.le_refl x⟩
  comp f g := ⟨Preorder.le_trans f.down g.down⟩
  comp_id _ := plift_subsingleton _ _
  id_comp _ := plift_subsingleton _ _
  assoc _ _ _ := plift_subsingleton _ _

/-! ## Closure operators -/

/-- A closure operator on a preorder: monotone, inflationary, idempotent.  This is
the *unifying-completeness (tightness)* interface: supplying it for a concrete
engine is that engine's tightness theorem. -/
class Closure (α : Type u) [Preorder α] where
  /-- The closure map (saturation to a fixed point). -/
  cl : α → α
  /-- Monotone: closure respects entailment. -/
  mono : {x y : α} → Preorder.le x y → Preorder.le (cl x) (cl y)
  /-- Inflationary: closure only adds consequences. -/
  infl : (x : α) → Preorder.le x (cl x)
  /-- Idempotent: closure terminates at a fixed point. -/
  idem : (x : α) → cl (cl x) = cl x

/-- The reflective subcategory: the **saturated** (closed) configurations, i.e. the
fixed points of `cl`. -/
structure Fixed (α : Type u) [Preorder α] [Closure α] where
  /-- The underlying configuration. -/
  val : α
  /-- Witness that it is saturated. -/
  closed : Closure.cl val = val

/-- The saturated subcategory is again thin, with the entailment order inherited on
underlying points. -/
instance Fixed.toCat (α : Type u) [Preorder α] [Closure α] : Category (Fixed α) where
  Hom a b := PLift (Preorder.le a.val b.val)
  id a := ⟨Preorder.le_refl a.val⟩
  comp f g := ⟨Preorder.le_trans f.down g.down⟩
  comp_id _ := plift_subsingleton _ _
  id_comp _ := plift_subsingleton _ _
  assoc _ _ _ := plift_subsingleton _ _

section
variable (α : Type u) [Preorder α] [Closure α]

/-- The inclusion `i : Fixed α ⥤ α` of the saturated subcategory.  On morphisms it is
the identity (a saturated entailment *is* an entailment). -/
def include' : Fixed α ⥤ α where
  obj a := a.val
  map f := ⟨f.down⟩
  map_id _ := plift_subsingleton _ _
  map_comp _ _ := plift_subsingleton _ _

/-- The reflector `saturate : α ⥤ Fixed α`: saturation, landing in the fixed points
(`idem` witnesses that `cl x` is closed).  Functorial by `mono`. -/
def saturate : α ⥤ Fixed α where
  obj x := ⟨Closure.cl x, Closure.idem x⟩
  map f := ⟨Closure.mono f.down⟩
  map_id _ := plift_subsingleton _ _
  map_comp _ _ := plift_subsingleton _ _

/-- **The reflection**: saturation is left adjoint to the inclusion of the saturated
subcategory.  The unit is `infl` (`x ⟶ cl x`); the counit, at a saturated `d`, is
`cl d = d` raised to a morphism by reflexivity.  Both triangle identities (and the
naturality of unit and counit) are thinness. -/
def reflection : Adjunction (saturate α) (include' α) where
  unit :=
    { app := fun x => ⟨Closure.infl x⟩
      naturality := fun _ => plift_subsingleton _ _ }
  counit :=
    { app := fun d =>
        ⟨cast (congrArg (fun t => Preorder.le t d.val) d.closed).symm
          (Preorder.le_refl d.val)⟩
      naturality := fun _ => plift_subsingleton _ _ }
  triangle_left _ := plift_subsingleton _ _
  triangle_right _ := plift_subsingleton _ _

/-! ## The saturation Kan extension -/

/-- **The capstone.**  The inclusion of the saturated subcategory is the left Kan
extension of the identity along saturation:

  `include' = Lan_saturate (Id)`.

Obtained from the reflection adjunction via `comp-cat-theory`'s `adjToLan`. -/
def lan : LeftKanExtension (saturate α) (idFunctor α) :=
  adjToLan (reflection α)

/-- The dual capstone.  Saturation itself is the right Kan extension of the identity
along the inclusion:

  `saturate = Ran_include' (Id)`.

Obtained from the same adjunction via `adjToRan`. -/
def ran : RightKanExtension (include' α) (idFunctor (Fixed α)) :=
  adjToRan (reflection α)

end

/-! ## A worked instance

A fully-proven, axiom-clean instantiation of the whole pipeline, demonstrating that
`Closure` is inhabited and that `lan`/`ran` compute.  We take the
two-point entailment preorder on `Bool` (`false ≤ everything`, `true ≤ true`) and
the closure "saturate to ⊤".  Its reflective subcategory is the terminal `{⊤}`:
saturation reflects every truth-value onto the single saturated object. -/

namespace Example

/-- Truth-values ordered by implication: `a ≤ b` iff `a` true forces `b` true. -/
instance boolPre : Preorder Bool where
  le a b := a = true → b = true
  le_refl _ := fun h => h
  le_trans f g := fun h => g (f h)

/-- "Saturate to ⊤": the constant-`true` closure on `boolPre`. -/
instance satToTop : Closure Bool where
  cl _ := true
  mono _ := fun h => h
  infl _ := fun _ => rfl
  idem _ := rfl

/-- The saturation Kan extension for "saturate to ⊤" computes. -/
def satToTopLan : LeftKanExtension (saturate Bool) (idFunctor Bool) :=
  lan Bool

/-- And its dual. -/
def satToTopRan : RightKanExtension (include' Bool) (idFunctor (Fixed Bool)) :=
  ran Bool

end Example

end Reflector

end KanSaturation
