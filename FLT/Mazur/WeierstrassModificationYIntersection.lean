/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationYOpenMaps
public import FLT.Mazur.PrincipalOpenIntersectionModels

/-!
# The actual intersection of the two y-chart ratio opens

The product localization is the scheme-theoretic intersection. Its two
restriction maps are explicit algebra maps, so coordinate substitutions can
be compared without unfolding a tensor-product presentation of a pullback.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassModificationY

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The ring of the common ratio principal open D(r*u). -/
abbrev RatioIntersection :=
  Localization.Away (coord W s b3 b4 b6 0 * coord W s b3 b4 b6 1)

/-- Both ratios become units on the actual intersection. -/
theorem intersection_ratios_isUnit :
    IsUnit (algebraMap _ (RatioIntersection W s b3 b4 b6) (coord W s b3 b4 b6 0)) ∧
    IsUnit (algebraMap _ (RatioIntersection W s b3 b4 b6) (coord W s b3 b4 b6 1)) := by
  rw [← IsUnit.mul_iff, ← map_mul]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- Restriction of scale-open functions to the intersection. -/
def intersectionScale : ScaleOpen W s b3 b4 b6 →ₐ[R] RatioIntersection W s b3 b4 b6 :=
  IsLocalization.Away.liftAlgHom (coord W s b3 b4 b6 0)
    (f := IsScalarTower.toAlgHom R _ _) (intersection_ratios_isUnit W s b3 b4 b6).1

/-- Restriction of horizontal-open functions to the intersection. -/
def intersectionHorizontal :
    HorizontalOpen W s b3 b4 b6 →ₐ[R] RatioIntersection W s b3 b4 b6 :=
  IsLocalization.Away.liftAlgHom (coord W s b3 b4 b6 1)
    (f := IsScalarTower.toAlgHom R _ _) (intersection_ratios_isUnit W s b3 b4 b6).2

/-- Scale restriction retains the original y-chart functions. -/
@[simp] theorem intersectionScale_base (z : Coordinate W s b3 b4 b6) :
    intersectionScale W s b3 b4 b6 (algebraMap _ _ z) = algebraMap _ _ z := by
  rw [intersectionScale, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- Horizontal restriction retains the original y-chart functions. -/
@[simp] theorem intersectionHorizontal_base (z : Coordinate W s b3 b4 b6) :
    intersectionHorizontal W s b3 b4 b6 (algebraMap _ _ z) = algebraMap _ _ z := by
  rw [intersectionHorizontal, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The scale restriction as an actual scheme morphism. -/
def intersectionToScale : Spec (.of (RatioIntersection W s b3 b4 b6)) ⟶
    Spec (.of (ScaleOpen W s b3 b4 b6)) :=
  Spec.map (CommRingCat.ofHom (intersectionScale W s b3 b4 b6).toRingHom)

/-- The horizontal restriction as an actual scheme morphism. -/
def intersectionToHorizontal : Spec (.of (RatioIntersection W s b3 b4 b6)) ⟶
    Spec (.of (HorizontalOpen W s b3 b4 b6)) :=
  Spec.map (CommRingCat.ofHom (intersectionHorizontal W s b3 b4 b6).toRingHom)

/-- Scale restriction commutes with the original chart inclusions. -/
@[reassoc] theorem intersectionToScale_fac :
    intersectionToScale W s b3 b4 b6 ≫
        PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 0) =
      PrincipalAffineRefinement.inclusion
        (coord W s b3 b4 b6 0 * coord W s b3 b4 b6 1) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact intersectionScale_base W s b3 b4 b6

/-- Horizontal restriction commutes with the original chart inclusions. -/
@[reassoc] theorem intersectionToHorizontal_fac :
    intersectionToHorizontal W s b3 b4 b6 ≫
        PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 1) =
      PrincipalAffineRefinement.inclusion
        (coord W s b3 b4 b6 0 * coord W s b3 b4 b6 1) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact intersectionHorizontal_base W s b3 b4 b6

/-- The explicit scale restriction equals the canonical open inclusion. -/
theorem intersectionToScale_eq : intersectionToScale W s b3 b4 b6 =
    PrincipalLocalizationSquare.openInclusion (PrimeSpectrum.basicOpen_mul_le_left
      (coord W s b3 b4 b6 0) (coord W s b3 b4 b6 1)) := by
  rw [← cancel_mono (PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 0))]
  exact (intersectionToScale_fac W s b3 b4 b6).trans
    (PrincipalLocalizationSquare.openInclusion_fac _).symm

/-- The explicit horizontal restriction equals the canonical open inclusion. -/
theorem intersectionToHorizontal_eq : intersectionToHorizontal W s b3 b4 b6 =
    PrincipalLocalizationSquare.openInclusion (PrimeSpectrum.basicOpen_mul_le_right
      (coord W s b3 b4 b6 0) (coord W s b3 b4 b6 1)) := by
  rw [← cancel_mono (PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 1))]
  exact (intersectionToHorizontal_fac W s b3 b4 b6).trans
    (PrincipalLocalizationSquare.openInclusion_fac _).symm

/-- The product localization is the actual scheme-theoretic overlap of the ratio cover. -/
theorem ratioIntersection_isPullback :
    IsPullback (intersectionToScale W s b3 b4 b6) (intersectionToHorizontal W s b3 b4 b6)
      (PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 0))
      (PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 1)) := by
  rw [intersectionToScale_eq, intersectionToHorizontal_eq]
  exact PrincipalLocalizationSquare.product_isPullback _ _

end FLT.Mazur.WeierstrassModificationY
