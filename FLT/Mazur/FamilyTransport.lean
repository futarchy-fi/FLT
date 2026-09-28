/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FCurveContracts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Transport of proper flat families

The core family properties are preserved by arbitrary base change and by isomorphisms
in `Over S`. The pullback convention is `X ×[S] T`, with second projection to `T`.
Identity and composite comparisons are isomorphisms over their bases; their equations
also expose the projections to the original total space. No condition on the base
or the base-change morphism is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve

variable {S T U : Scheme.{u}}

/-- Properness is invariant under an isomorphism over an arbitrary base. -/
theorem isProper_iff_of_overIso {X Y : Over S} (e : X ≅ Y) :
    IsProper X.hom ↔ IsProper Y.hom := by
  rw [← Over.w e.hom]
  exact MorphismProperty.cancel_left_of_respectsIso @IsProper e.hom.left Y.hom

/-- Flatness is invariant under an isomorphism over an arbitrary base. -/
theorem flat_iff_of_overIso {X Y : Over S} (e : X ≅ Y) :
    Flat X.hom ↔ Flat Y.hom := by
  constructor
  · intro hX
    let := hX
    rw [← Over.w e.inv]
    infer_instance
  · intro hY
    let := hY
    rw [← Over.w e.hom]
    infer_instance

/-- Local finite presentation is invariant under an isomorphism over the base. -/
theorem locallyOfFinitePresentation_iff_of_overIso {X Y : Over S} (e : X ≅ Y) :
    LocallyOfFinitePresentation X.hom ↔ LocallyOfFinitePresentation Y.hom := by
  constructor
  · intro hX
    let := hX
    rw [← Over.w e.inv]
    infer_instance
  · intro hY
    let := hY
    rw [← Over.w e.hom]
    infer_instance

/-- Transport all three core properties along an over-isomorphism. -/
theorem properFlatFamily_iff_of_overIso {X Y : Over S} (e : X ≅ Y) :
    ProperFlatFamily X.hom ↔ ProperFlatFamily Y.hom := by
  unfold ProperFlatFamily
  rw [isProper_iff_of_overIso e, flat_iff_of_overIso e,
    locallyOfFinitePresentation_iff_of_overIso e]

/-- The arbitrary-base-change contract for the core family properties. -/
theorem properFlatBaseChange {X : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) :
    ProperFlatBaseChange f g := by
  intro ⟨hp, hf, hl⟩
  let := hp
  let := hf
  let := hl
  exact ⟨inferInstance, inferInstance, inferInstance⟩

namespace ProperFlatFamily

/-- A method form of the base-change theorem for later family records. -/
theorem baseChange {X : Scheme.{u}} {f : X ⟶ S} (hf : ProperFlatFamily f)
    (g : T ⟶ S) : ProperFlatFamily (pullback.snd f g) :=
  properFlatBaseChange f g hf

/-- A method form of transport along an over-isomorphism. -/
theorem of_overIso {X Y : Over S} (hX : ProperFlatFamily X.hom) (e : X ≅ Y) :
    ProperFlatFamily Y.hom :=
  (properFlatFamily_iff_of_overIso e).mp hX

end ProperFlatFamily

/-- Base change as an object over the new base, retaining its structure map. -/
abbrev familyPullback (X : Over S) (g : T ⟶ S) : Over T :=
  Over.mk (pullback.snd X.hom g)

@[simp]
theorem familyPullback_hom (X : Over S) (g : T ⟶ S) :
    (familyPullback X g).hom = pullback.snd X.hom g := rfl

/-- The first projection lies over the base-change map. -/
@[reassoc]
theorem familyPullback_fst_hom (X : Over S) (g : T ⟶ S) :
    pullback.fst X.hom g ≫ X.hom = (familyPullback X g).hom ≫ g :=
  pullback.condition

/-- The pullback object inherits the core family properties. -/
theorem properFlatFamily_familyPullback {X : Over S} (hX : ProperFlatFamily X.hom)
    (g : T ⟶ S) : ProperFlatFamily (familyPullback X g).hom :=
  hX.baseChange g

/-- Pulling back along the identity gives the original family over the same base. -/
def familyPullbackIdIso (X : Over S) : familyPullback X (𝟙 S) ≅ X :=
  Over.isoMk (asIso (pullback.fst X.hom (𝟙 S)))
    (by simpa using pullback.condition (f := X.hom) (g := 𝟙 S))

theorem familyPullbackIdIso_hom_left (X : Over S) :
    (familyPullbackIdIso X).hom.left = pullback.fst X.hom (𝟙 S) := rfl

@[reassoc]
theorem familyPullbackIdIso_hom_left_hom (X : Over S) :
    (familyPullbackIdIso X).hom.left ≫ X.hom =
      pullback.snd X.hom (𝟙 S) :=
  Over.w (familyPullbackIdIso X).hom

@[reassoc (attr := simp)]
theorem familyPullbackIdIso_inv_left_fst (X : Over S) :
    (familyPullbackIdIso X).inv.left ≫ pullback.fst X.hom (𝟙 S) = 𝟙 X.left := by
  simp [familyPullbackIdIso]

@[reassoc (attr := simp)]
theorem familyPullbackIdIso_inv_left_hom (X : Over S) :
    (familyPullbackIdIso X).inv.left ≫ pullback.snd X.hom (𝟙 S) = X.hom :=
  Over.w (familyPullbackIdIso X).inv

/-- Iterated pullback agrees with pullback along the composite, over the final base. -/
def familyPullbackCompIso (X : Over S) (g : T ⟶ S) (h : U ⟶ T) :
    familyPullback (familyPullback X g) h ≅ familyPullback X (h ≫ g) :=
  Over.isoMk (pullbackLeftPullbackSndIso X.hom g h)
    (pullbackLeftPullbackSndIso_hom_snd X.hom g h)

/-- The composite comparison preserves the projection to the original total space. -/
@[reassoc (attr := simp)]
theorem familyPullbackCompIso_hom_left_fst (X : Over S) (g : T ⟶ S) (h : U ⟶ T) :
    (familyPullbackCompIso X g h).hom.left ≫ pullback.fst X.hom (h ≫ g) =
      pullback.fst (pullback.snd X.hom g) h ≫ pullback.fst X.hom g :=
  pullbackLeftPullbackSndIso_hom_fst X.hom g h

/-- The composite comparison preserves the structure map to the final base. -/
@[reassoc (attr := simp)]
theorem familyPullbackCompIso_hom_left_hom (X : Over S) (g : T ⟶ S) (h : U ⟶ T) :
    (familyPullbackCompIso X g h).hom.left ≫ pullback.snd X.hom (h ≫ g) =
      pullback.snd (pullback.snd X.hom g) h :=
  Over.w (familyPullbackCompIso X g h).hom

/-- The inverse comparison also preserves the original total-space projection. -/
@[reassoc (attr := simp)]
theorem familyPullbackCompIso_inv_left_fst_fst (X : Over S) (g : T ⟶ S) (h : U ⟶ T) :
    (familyPullbackCompIso X g h).inv.left ≫
        pullback.fst (pullback.snd X.hom g) h ≫ pullback.fst X.hom g =
      pullback.fst X.hom (h ≫ g) :=
  pullbackLeftPullbackSndIso_inv_fst X.hom g h

@[reassoc (attr := simp)]
theorem familyPullbackCompIso_inv_left_hom (X : Over S) (g : T ⟶ S) (h : U ⟶ T) :
    (familyPullbackCompIso X g h).inv.left ≫
        pullback.snd (pullback.snd X.hom g) h =
      pullback.snd X.hom (h ≫ g) :=
  Over.w (familyPullbackCompIso X g h).inv

end FLT.Mazur.FCurve
