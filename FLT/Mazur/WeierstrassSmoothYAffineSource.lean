/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRelativeSmoothOpen
public import FLT.Mazur.WeierstrassChartEvaluationComparison
public import Mathlib.RingTheory.Smooth.Flat

/-!
# An integral smooth source with actual Y and affine presentations

Invert the free Z derivative in the Y chart, then its Z coordinate. This
retains an integral flat source for conormal calculations and constructs both
chart presentations of the same actual smooth point.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The free Z-derivative chart in the original Y chart. -/
abbrev SmoothYDerivativeRing := Localization.Away (chartPartial W 1 2)

/-- Its affine part, before any passage to the residue field. -/
abbrev SmoothYAffineRing := Localization.Away
  (algebraMap (Coordinate W 1) (SmoothYDerivativeRing W) (coord W 1 2))

/-- The retained original normalized Y presentation. -/
def smoothYAffineY : Coordinate W 1 →ₐ[R] SmoothYAffineRing W :=
  IsScalarTower.toAlgHom R (Coordinate W 1) (SmoothYAffineRing W)

/-- Z is invertible on the constructed common source. -/
theorem smoothYAffine_z_unit : IsUnit (smoothYAffineY W (coord W 1 2)) := by
  change IsUnit (algebraMap (Coordinate W 1) (SmoothYAffineRing W) _)
  rw [IsScalarTower.algebraMap_apply (Coordinate W 1)
    (SmoothYDerivativeRing W) (SmoothYAffineRing W)]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The actual original Y/Z overlap map. -/
def smoothYAffineOverlap : Overlap W 1 2 →ₐ[R] SmoothYAffineRing W :=
  IsLocalization.Away.liftAlgHom (coord W 1 2) (smoothYAffine_z_unit W)

/-- Restriction to the overlap preserves every original Y-chart function. -/
theorem smoothYAffineOverlap_base (q : Coordinate W 1) :
    smoothYAffineOverlap W (algebraMap (Coordinate W 1) (Overlap W 1 2) q) =
      smoothYAffineY W q :=
  IsLocalization.Away.lift_eq (coord W 1 2) (smoothYAffine_z_unit W) q

/-- The actual affine presentation is constructed by the original chart transition. -/
def smoothYAffineA : Coordinate W 2 →ₐ[R] SmoothYAffineRing W :=
  (smoothYAffineOverlap W).comp (transitionBase W 1 2)

/-- The two constructed presentations are the same point of the original cubic. -/
theorem smoothYAffine_common :
    Spec.map (CommRingCat.ofHom (smoothYAffineA W).toRingHom) ≫ integralCurveChart W 2 =
      Spec.map (CommRingCat.ofHom (smoothYAffineY W).toRingHom) ≫ integralCurveChart W 1 := by
  apply (chart_algHom_global_eq_iff W 2 1 _ _).mpr
  intro i
  simp only [smoothYAffineA, AlgHom.comp_apply, transitionBase_coord, map_mul,
    overlapCoord, smoothYAffineOverlap_base, coord_self, map_one, mul_one]

/-- The constructed source maps to the actual relative smooth locus. -/
def smoothYAffinePoint : Spec (.of (SmoothYAffineRing W)) ⟶
    (integralSmoothOpen W).toScheme :=
  Spec.map (CommRingCat.ofHom (algebraMap (SmoothYDerivativeRing W) (SmoothYAffineRing W))) ≫
    chartPartialToSmooth W 1 2 (by decide)

/-- Its smooth point retains the original normalized Y presentation. -/
theorem smoothYAffinePoint_inclusion :
    smoothYAffinePoint W ≫ (integralSmoothOpen W).ι =
      Spec.map (CommRingCat.ofHom (smoothYAffineY W).toRingHom) ≫ integralCurveChart W 1 := by
  rw [smoothYAffinePoint, Category.assoc, chartPartialToSmooth_inclusion,
    PrincipalAffineRefinement.inclusion, ← Category.assoc, ← Spec.map_comp]
  rfl

/-- The affine presentation is the genuine smooth point, not an extra identification. -/
theorem smoothYAffineA_inclusion :
    Spec.map (CommRingCat.ofHom (smoothYAffineA W).toRingHom) ≫ integralCurveChart W 2 =
      smoothYAffinePoint W ≫ (integralSmoothOpen W).ι := by
  rw [smoothYAffinePoint_inclusion, smoothYAffine_common]

/-- The integral common source is flat over the original coefficient ring. -/
instance smoothYAffine_flat : Module.Flat R (SmoothYAffineRing W) := by
  let _ := chartPartial_smooth W 1 2 (by decide)
  let _ : Module.Flat (SmoothYDerivativeRing W) (SmoothYAffineRing W) :=
    IsLocalization.flat _ (Submonoid.powers
      (algebraMap (Coordinate W 1) (SmoothYDerivativeRing W) (coord W 1 2)))
  exact Module.Flat.trans R (SmoothYDerivativeRing W) (SmoothYAffineRing W)

end FLT.Mazur.WeierstrassIntegralChart
