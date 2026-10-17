/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingTwoCoefficientScaling

/-!
# Independent branch scaling with a changed smoothing parameter

Two arbitrary coefficient units give an isomorphism to a different smoothing.
The target parameter is their product times the source parameter. No relation
requiring that product to fix the original parameter is imposed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonSmoothing
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (t s : R) (a b : Rˣ)
  (h : (a : R) * b * t = s)

/-- Pull back the two target coordinates with their independently chosen units. -/
def changeParameter : ChartRing s →ₐ[R] ChartRing t :=
  evaluate s (algebraMap R _ a * leftCoordinate t)
    (algebraMap R _ b * rightCoordinate t) (by
      rw [mul_mul_mul_comm, coordinate_relation, ← map_mul, ← map_mul, h])

/-- The first coordinate keeps its full coefficient. -/
@[simp] theorem changeParameter_left :
    changeParameter t s a b h (leftCoordinate s) =
      algebraMap R _ a * leftCoordinate t := evaluate_left ..

/-- The second coordinate keeps its independent full coefficient. -/
@[simp] theorem changeParameter_right :
    changeParameter t s a b h (rightCoordinate s) =
      algebraMap R _ b * rightCoordinate t := evaluate_right ..

include h in
/-- The inverse weights recover the original smoothing parameter. -/
theorem changeParameter_inverse_relation : (↑a⁻¹ : R) * ↑b⁻¹ * s = t := by
  rw [← h]
  calc
    _ = ((↑a⁻¹ : R) * a) * ((↑b⁻¹ : R) * b) * t := by ring
    _ = t := by rw [Units.inv_mul, Units.inv_mul, one_mul, one_mul]

/-- Independent scaling is invertible on the entire changed smoothing. -/
def changeParameterEquiv : ChartRing s ≃ₐ[R] ChartRing t :=
  { changeParameter t s a b h with
    invFun := changeParameter s t a⁻¹ b⁻¹ (changeParameter_inverse_relation t s a b h)
    left_inv := fun x ↦ by
      have he :
          (changeParameter s t a⁻¹ b⁻¹ (changeParameter_inverse_relation t s a b h)).comp
            (changeParameter t s a b h) = AlgHom.id R (ChartRing s) := by
        apply chartRing_hom_ext s <;> simp <;> simp [← mul_assoc, ← map_mul]
      exact DFunLike.congr_fun he x
    right_inv := fun x ↦ by
      have he : (changeParameter t s a b h).comp
          (changeParameter s t a⁻¹ b⁻¹ (changeParameter_inverse_relation t s a b h)) =
            AlgHom.id R (ChartRing t) := by
        apply chartRing_hom_ext t <;> simp <;> simp [← mul_assoc, ← map_mul]
      exact DFunLike.congr_fun he x }

/-- The whole source chart is isomorphic to the chart with the changed parameter. -/
def changeParameterIso : chart R t ≅ chart R s :=
  Scheme.Spec.mapIso (changeParameterEquiv t s a b h).toRingEquiv.toCommRingCatIso.op

/-- The first full Laurent boundary scales by precisely the first unit. -/
theorem leftLaurentMap_changeParameter :
    (leftLaurentMap t).comp (changeParameter t s a b h) =
      (PolygonScaledReciprocal.scaling a).comp (leftLaurentMap s) := by
  apply chartRing_hom_ext s
  · simp [PolygonScaledReciprocal.scaling, AlgHom.coe_mk]
  · simp only [AlgHom.comp_apply, changeParameter_right, map_mul, AlgHom.commutes,
      leftLaurentMap_right, PolygonScaledReciprocal.scaling, AlgHom.coe_mk,
      PolygonChartScaling.laurent_C, PolygonChartScaling.laurent_T_neg_one]
    change LaurentPolynomial.C (b : R) * (LaurentPolynomial.C t *
      LaurentPolynomial.T (-1)) = LaurentPolynomial.C s *
        (LaurentPolynomial.C (↑a⁻¹ : R) * LaurentPolynomial.T (-1))
    rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul]
    congr 2
    rw [← h]
    rw [show (a : R) * b * t * ↑a⁻¹ = ((a : R) * ↑a⁻¹) * (b * t) by ring,
      Units.mul_inv, one_mul]

/-- The second full Laurent boundary scales by precisely the second unit. -/
theorem rightLaurentMap_changeParameter :
    ((leftLaurentMap t).comp (branchSwapMap t)).comp (changeParameter t s a b h) =
      (PolygonScaledReciprocal.scaling b).comp
        ((leftLaurentMap s).comp (branchSwapMap s)) := by
  apply chartRing_hom_ext s
  · simp only [AlgHom.comp_apply, changeParameter_left, map_mul, AlgHom.commutes,
      branchSwapMap_left, leftLaurentMap_right, PolygonScaledReciprocal.scaling, AlgHom.coe_mk,
      PolygonChartScaling.laurent_C, PolygonChartScaling.laurent_T_neg_one]
    change LaurentPolynomial.C (a : R) * (LaurentPolynomial.C t *
      LaurentPolynomial.T (-1)) = LaurentPolynomial.C s *
        (LaurentPolynomial.C (↑b⁻¹ : R) * LaurentPolynomial.T (-1))
    rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul]
    congr 2
    rw [← h]
    rw [show (a : R) * b * t * ↑b⁻¹ = ((b : R) * ↑b⁻¹) * (a * t) by ring,
      Units.mul_inv, one_mul]
  · simp [PolygonScaledReciprocal.scaling, AlgHom.coe_mk]

/-- The first puncture square commutes for the entire changed chart. -/
@[reassoc] theorem leftBranch_changeParameter :
    leftBranchOpen R t ≫ (changeParameterIso t s a b h).hom =
      (edgeScalingIso a).hom ≫ leftBranchOpen R s := by
  rw [leftBranchOpen_eq_spec, leftBranchOpen_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext
    (congrArg AlgHom.toRingHom (leftLaurentMap_changeParameter t s a b h)))

/-- The second puncture uses its own coefficient on the same chart. -/
@[reassoc] theorem rightBranch_changeParameter :
    rightBranchOpen R t ≫ (changeParameterIso t s a b h).hom =
      (edgeScalingIso b).hom ≫ rightBranchOpen R s := by
  rw [rightBranchOpen_eq_spec, rightBranchOpen_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext
    (congrArg AlgHom.toRingHom (rightLaurentMap_changeParameter t s a b h)))

/-- Changing the smoothing does not change the coefficient structure. -/
@[reassoc] theorem changeParameterIso_base :
    (changeParameterIso t s a b h).hom ≫ chartStructure R s = chartStructure R t := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (changeParameter t s a b h).comp_algebraMap)

end FLT.Mazur.PolygonSmoothing
