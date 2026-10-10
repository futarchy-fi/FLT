/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityNegationAddition
public import FLT.Mazur.WeierstrassNegationAdditionDescent

/-!
# A concrete infinity neighborhood for the inverse identity

Pull the infinity addition domain back along the actual negation pair and invert
an extra factor that is one at zero. The resulting open maps to the original
addition domain and its normalized output is identically the zero section.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Simultaneously invert the slope denominator and the extra inverse-formula factor. -/
def infinityInverseDen : InfinityNegationOpen W :=
  infinityNegationFactor W * infinityNegationInput W (infinityDen W (AlgHom.id R _))


/-- The slope neighborhood inside the original negation neighborhood. -/
def InfinityInverseSlopeOpen := Localization.Away (infinityInverseDen W)

instance : CommRing (InfinityInverseSlopeOpen W) :=
  inferInstanceAs (CommRing (Localization.Away (infinityInverseDen W)))

instance : Algebra R (InfinityInverseSlopeOpen W) :=
  inferInstanceAs (Algebra R (Localization.Away (infinityInverseDen W)))

instance : Algebra (InfinityNegationOpen W) (InfinityInverseSlopeOpen W) :=
  inferInstanceAs (Algebra (InfinityNegationOpen W) (Localization.Away (infinityInverseDen W)))

instance : IsScalarTower R (InfinityNegationOpen W) (InfinityInverseSlopeOpen W) :=
  inferInstanceAs (IsScalarTower R (InfinityNegationOpen W)
    (Localization.Away (infinityInverseDen W)))

instance : IsLocalization.Away (infinityInverseDen W) (InfinityInverseSlopeOpen W) :=
  inferInstanceAs (IsLocalization.Away (infinityInverseDen W)
    (Localization.Away (infinityInverseDen W)))

attribute [irreducible] InfinityInverseSlopeOpen

/-- Restriction from the original negation neighborhood. -/
def infinityInverseSlopeRestriction :
    InfinityNegationOpen W →ₐ[R] InfinityInverseSlopeOpen W :=
  IsScalarTower.toAlgHom R _ _

/-- Both factors of the localized denominator are invertible. -/
theorem infinityInverseDen_factors :
    IsUnit (infinityInverseSlopeRestriction W (infinityNegationFactor W)) ∧
      IsUnit (((infinityInverseSlopeRestriction W).comp (infinityNegationInput W))
        (infinityDen W (AlgHom.id R _))) := by
  have h := IsLocalization.Away.algebraMap_isUnit (infinityInverseDen W)
    (S := InfinityInverseSlopeOpen W)
  change IsUnit (infinityInverseSlopeRestriction W (infinityInverseDen W)) at h
  change IsUnit (infinityInverseSlopeRestriction W (infinityNegationFactor W *
    infinityNegationInput W (infinityDen W (AlgHom.id R _)))) at h
  rw [map_mul] at h
  exact (Commute.all _ _).isUnit_mul_iff.mp h

/-- The pulled-back domain maps to the actual infinity slope domain. -/
def infinityInverseSlopeMap : InfinitySlopeOpen W →ₐ[R] InfinityInverseSlopeOpen W :=
  IsLocalization.Away.liftAlgHom (infinityDen W (AlgHom.id R _))
    (infinityInverseDen_factors W).2

/-- The slope map retains exactly the actual inverse pair. -/
theorem infinityInverseSlopeMap_inputs :
    (infinityInverseSlopeMap W).comp (infinitySlopeRestriction W) =
      (infinityInverseSlopeRestriction W).comp (infinityNegationInput W) := by
  apply AlgHom.ext
  intro a
  change infinityInverseSlopeMap W (algebraMap _ _ a) = _
  simp only [infinityInverseSlopeMap, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

/-- The output normalizing coordinate on the pulled-back slope domain. -/
def infinityInverseOutputY : InfinityInverseSlopeOpen W :=
  infinityInverseSlopeMap W (infinityOutputCoordinates W 1)


/-- The full inverse neighborhood, with normalized output. -/
def InfinityInverseOpen := Localization.Away (infinityInverseOutputY W)

instance : CommRing (InfinityInverseOpen W) :=
  inferInstanceAs (CommRing (Localization.Away (infinityInverseOutputY W)))

instance : Algebra R (InfinityInverseOpen W) :=
  inferInstanceAs (Algebra R (Localization.Away (infinityInverseOutputY W)))

instance : Algebra (InfinityInverseSlopeOpen W) (InfinityInverseOpen W) :=
  inferInstanceAs (Algebra (InfinityInverseSlopeOpen W)
    (Localization.Away (infinityInverseOutputY W)))

instance : IsScalarTower R (InfinityInverseSlopeOpen W) (InfinityInverseOpen W) :=
  inferInstanceAs (IsScalarTower R (InfinityInverseSlopeOpen W)
    (Localization.Away (infinityInverseOutputY W)))

instance : IsLocalization.Away (infinityInverseOutputY W) (InfinityInverseOpen W) :=
  inferInstanceAs (IsLocalization.Away (infinityInverseOutputY W)
    (Localization.Away (infinityInverseOutputY W)))

attribute [irreducible] InfinityInverseOpen

/-- The final output localization. -/
def infinityInverseOutputRestriction : InfinityInverseSlopeOpen W →ₐ[R] InfinityInverseOpen W :=
  IsScalarTower.toAlgHom R _ _

/-- Restrict the original negation neighborhood to the full inverse neighborhood. -/
def infinityInverseNegationRestriction : InfinityNegationOpen W →ₐ[R] InfinityInverseOpen W :=
  (infinityInverseOutputRestriction W).comp (infinityInverseSlopeRestriction W)

/-- Restrict the original Y chart to the full inverse neighborhood. -/
def infinityInverseRestriction : Coordinate W 1 →ₐ[R] InfinityInverseOpen W :=
  (infinityInverseNegationRestriction W).comp (infinityNegationRestriction W)

/-- The new neighborhood maps to the original normalized infinity addition domain. -/
def infinityInverseMap : InfinityAdditionOpen W →ₐ[R] InfinityInverseOpen W :=
  IsLocalization.Away.liftAlgHom (A := R) (P := InfinityInverseOpen W)
    (f := (infinityInverseOutputRestriction W).comp (infinityInverseSlopeMap W))
    (infinityOutputCoordinates W 1)
    (show IsUnit (((infinityInverseOutputRestriction W).comp
      (infinityInverseSlopeMap W)) (infinityOutputCoordinates W 1)) from
      IsLocalization.Away.algebraMap_isUnit (S := InfinityInverseOpen W)
        (infinityInverseOutputY W))

/-- The addition-domain map retains the slope-domain map. -/
theorem infinityInverseMap_output :
    (infinityInverseMap W).comp (infinityOutputRestriction W) =
      (infinityInverseOutputRestriction W).comp (infinityInverseSlopeMap W) := by
  apply AlgHom.ext
  intro a
  change infinityInverseMap W (algebraMap _ _ a) = _
  simp only [infinityInverseMap, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

/-- The full addition-domain square retains the actual inverse pair. -/
theorem infinityInverseMap_inputs :
    (infinityInverseMap W).comp (infinityAdditionRestriction W) =
      (infinityInverseNegationRestriction W).comp (infinityNegationInput W) := by
  rw [infinityAdditionRestriction, ← AlgHom.comp_assoc, infinityInverseMap_output,
    AlgHom.comp_assoc, infinityInverseSlopeMap_inputs, ← AlgHom.comp_assoc]
  rfl

/-- The normalized addition map is zero on the entire inverse neighborhood. -/
theorem infinityInverseMap_addition :
    (infinityInverseMap W).comp (infinityAdditionChart W) =
      chartInfinityEvaluation (S := InfinityInverseOpen W) W :=
  infinityAdditionChart_negation (S := InfinityInverseOpen W) W
    (infinityInverseNegationRestriction W) (infinityInverseMap W) (infinityInverseMap_inputs W)
    ((infinityInverseDen_factors W).1.map (infinityInverseOutputRestriction W))

/-- Inclusion of the explicit inverse neighborhood into the Y chart. -/
def infinityInverseInclusion : Spec (.of (InfinityInverseOpen W)) ⟶ chartScheme W 1 :=
  Spec.map (CommRingCat.ofHom (infinityInverseRestriction W).toRingHom)

/-- All three localizations are open immersions, as is their composite. -/
instance infinityInverseInclusion_isOpenImmersion :
    IsOpenImmersion (infinityInverseInclusion W) := by
  have h₀ : IsOpenImmersion (Spec.map
      (CommRingCat.ofHom (infinityNegationRestriction W).toRingHom)) :=
    infinityNegationInclusion_isOpenImmersion W
  have h₁ : IsOpenImmersion (Spec.map
      (CommRingCat.ofHom (infinityInverseSlopeRestriction W).toRingHom)) :=
    IsOpenImmersion.of_isLocalization (infinityInverseDen W)
  have h₂ : IsOpenImmersion (Spec.map
      (CommRingCat.ofHom (infinityInverseOutputRestriction W).toRingHom)) :=
    IsOpenImmersion.of_isLocalization (infinityInverseOutputY W)
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (((infinityInverseOutputRestriction W).toRingHom.comp
      (infinityInverseSlopeRestriction W).toRingHom).comp
        (infinityNegationRestriction W).toRingHom)))
  simp only [CommRingCat.ofHom_comp, Spec.map_comp]
  infer_instance

end FLT.Mazur.WeierstrassIntegralChart
