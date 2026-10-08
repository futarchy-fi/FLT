/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartJacobianCover
public import FLT.Mazur.WeierstrassChartStandardSmooth
public import FLT.Mazur.WeierstrassIntegralCurveMorphisms
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smoothness of the actual integral cubic of unit discriminant

Each free-derivative localization has an explicit submersive presentation of
relative dimension one. The derivative cover and the original cubic atlas
then descend this property to the actual glued structure morphism.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The free-derivative open is smooth of relative dimension one over the original base. -/
theorem chartPartial_structure_smooth_dimension (j i : Fin 3) (hij : i ≠ j) :
    SmoothOfRelativeDimension 1
      (PrincipalAffineRefinement.inclusion (chartPartial W j i) ≫ chartStructure W j) := by
  change SmoothOfRelativeDimension 1 (Spec.map _ ≫ Spec.map _)
  rw [← Spec.map_comp]
  change SmoothOfRelativeDimension 1
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (chartPartial W j i)))))
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mpr
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr
    (chartPartial_standardSmooth_dimension W j i hij)

/-- The unit discriminant makes the derivative opens cover each entire normalized chart. -/
theorem chartStructure_smooth_dimension (hΔ : IsUnit W.Δ) (j : Fin 3) :
    SmoothOfRelativeDimension 1 (chartStructure W j) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover (chartPartialCover W hΔ j)).mpr
  intro i
  exact chartPartial_structure_smooth_dimension W j i.val i.property

/-- The whole glued cubic is smooth of relative dimension one when its discriminant is a unit. -/
theorem integralCurveStructure_smooth_dimension (hΔ : IsUnit W.Δ) :
    SmoothOfRelativeDimension 1 (integralCurveStructure W) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover (integralCurveOpenCover W)).mpr
  intro j
  change SmoothOfRelativeDimension 1 (integralCurveChart W j.down ≫ integralCurveStructure W)
  rw [integralCurveChart_structure]
  exact chartStructure_smooth_dimension W hΔ j.down

/-- Smoothness is proved for the actual model, independently of its group operations. -/
theorem integralCurveStructure_smooth (hΔ : IsUnit W.Δ) : Smooth (integralCurveStructure W) := by
  let _ := integralCurveStructure_smooth_dimension W hΔ
  exact SmoothOfRelativeDimension.smooth 1 _

end FLT.Mazur.WeierstrassIntegralChart
