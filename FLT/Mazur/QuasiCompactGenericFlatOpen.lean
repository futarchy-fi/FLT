/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineGenericFlatOpen
public import Mathlib.AlgebraicGeometry.Morphisms.Descent

/-!
# Generic flatness retaining a whole quasi-compact source

A finite affine open cover is assembled into one affine scheme. Generic
flatness of its actual composite supplies a single nonzero denominator.
Source locality then proves flatness of the entire original source pullback.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.QuasiCompactGenericFlatOpen
set_option backward.isDefEq.respectTransparency false
variable (X : Scheme) [CompactSpace X]
local notation "C" => X.affineCover.finiteSubcover

/-- One affine scheme contains all charts of the finite cover, without selecting a branch. -/
def affineCoverSource : Scheme := ∐ (fun a : (C).I₀ ↦ (C).X a)

instance affineCoverSource_isAffine : IsAffine (affineCoverSource X) := by
  unfold affineCoverSource
  infer_instance

/-- The actual covering morphism to the entire original source. -/
def affineCoverMap : affineCoverSource X ⟶ X := Sigma.desc (fun a ↦ (C).f a)

instance affineCoverMap_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (affineCoverMap X) :=
  IsZariskiLocalAtSource.sigmaDesc (fun _ ↦ inferInstance)

variable {X} {R : Type} [CommRing R] [IsDomain R]
  (g : X ⟶ Spec (.of R)) [LocallyOfFinitePresentation g]

/-- A single coefficient works simultaneously on the whole finite affine cover. -/
def coefficient : R := AffineGenericFlatOpen.coefficient (affineCoverMap X ≫ g)

theorem coefficient_ne_zero : coefficient g ≠ 0 :=
  AffineGenericFlatOpen.coefficient_ne_zero (affineCoverMap X ≫ g)

/-- The constructed dense principal open in the unchanged domain base. -/
def targetMap : Spec (.of (Localization.Away (coefficient g))) ⟶ Spec (.of R) :=
  AffineGenericFlatOpen.targetMap (affineCoverMap X ≫ g)

local notation "j" => targetMap g

instance targetMap_isOpenImmersion : IsOpenImmersion j :=
  AffineGenericFlatOpen.targetMap_isOpenImmersion (affineCoverMap X ≫ g)

instance targetMap_isDominant : IsDominant j :=
  AffineGenericFlatOpen.targetMap_isDominant (affineCoverMap X ≫ g)

/-- Flatness holds on the entire pullback, including every original affine chart. -/
instance projection_flat : Flat (pullback.fst j g) := by
  let p := affineCoverMap X
  let _ : Flat (pullback.fst j (p ≫ g)) :=
    AffineGenericFlatOpen.projection_flat (p ≫ g)
  let U := Scheme.Pullback.openCoverOfRight C j g
  apply IsZariskiLocalAtSource.of_openCover U
  intro a
  let z := Sigma.ι (fun a : (C).I₀ ↦ (C).X a) a
  have hz : z ≫ p = (C).f a := Sigma.ι_comp_desc _ _
  let e : pullback j ((C).f a ≫ g) ⟶ pullback j (p ≫ g) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ z) (by
      rw [Category.assoc, ← Category.assoc z, hz]
      exact pullback.condition)
  have he₁ : e ≫ pullback.fst j (p ≫ g) = pullback.fst j ((C).f a ≫ g) :=
    pullback.lift_fst _ _ _
  have he₂ : e ≫ pullback.snd j (p ≫ g) = pullback.snd j ((C).f a ≫ g) ≫ z :=
    pullback.lift_snd _ _ _
  have H : IsPullback e (pullback.snd j ((C).f a ≫ g))
      (pullback.snd j (p ≫ g)) z := by
    apply IsPullback.of_right _ he₂ (IsPullback.of_hasPullback j (p ≫ g))
    rw [he₁, ← Category.assoc, hz]
    exact IsPullback.of_hasPullback j ((C).f a ≫ g)
  let _ : IsOpenImmersion e := MorphismProperty.of_isPullback H.flip inferInstance
  have hf : Flat (pullback.fst j ((C).f a ≫ g)) := by
    rw [← he₁]
    infer_instance
  simpa only [U, Scheme.Pullback.openCoverOfRight_f, pullback.map, pullback.lift_fst,
    Category.comp_id] using hf

instance projection_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (pullback.fst j g) := inferInstance

instance projection_quasiCompact : QuasiCompact (pullback.fst j g) := inferInstance

/-- Surjectivity of a whole source is preserved; none is postulated if it was absent. -/
instance projection_surjective [Surjective g] : Surjective (pullback.fst j g) := inferInstance

end FLT.Mazur.QuasiCompactGenericFlatOpen
