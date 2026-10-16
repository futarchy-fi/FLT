/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingTwoCoefficientScaling

/-!
# Full puncture equations for two-coefficient smoothing automorphisms

The exact smoothing constraint gives both full Laurent boundary squares,
including their nilpotent terms. At zero parameter this recovers the
simultaneous independent correction, as an equality of entire chart isomorphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (t : R) (a b : Rˣ)
  (h : (a : R) * b * t = t)

include h in
/-- The other branch coefficient acts reciprocally on the full smoothing parameter. -/
theorem twoCoefficientScale_left_parameter : (b : R) * t = (↑a⁻¹ : R) * t := by
  have he := congrArg (fun z : R ↦ (↑a⁻¹ : R) * z) h
  simpa only [← mul_assoc, Units.inv_mul, one_mul] using he

include h in
/-- The same parameter relation holds with the two branch coefficients interchanged. -/
theorem twoCoefficientScale_right_parameter : (a : R) * t = (↑b⁻¹ : R) * t := by
  apply twoCoefficientScale_left_parameter t b a
  simpa only [mul_comm (b : R) (a : R)] using h

/-- The full outgoing Laurent restriction has exactly the prescribed first coefficient. -/
theorem leftLaurentMap_twoCoefficientScale :
    (leftLaurentMap t).comp (twoCoefficientScale t a b h) =
      (PolygonScaledReciprocal.scaling a).comp (leftLaurentMap t) := by
  apply chartRing_hom_ext t
  · simp [PolygonScaledReciprocal.scaling, AlgHom.coe_mk]
  · simp only [AlgHom.coe_comp, Function.comp_apply, twoCoefficientScale_right, map_mul,
      AlgHom.commutes, AddMonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self,
      RingHom.coe_id, id_eq, LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.T_zero,
      mul_one, leftLaurentMap_right, Int.reduceNeg, PolygonScaledReciprocal.scaling,
      AlgHom.coe_mk, PolygonChartScaling.laurent_C, PolygonChartScaling.laurent_T_neg_one]
    rw [← mul_assoc, ← map_mul, twoCoefficientScale_left_parameter t a b h]
    simp only [map_mul, mul_assoc, mul_left_comm]

/-- The full incoming Laurent restriction has exactly the independently prescribed coefficient. -/
theorem rightLaurentMap_twoCoefficientScale :
    ((leftLaurentMap t).comp (branchSwapMap t)).comp (twoCoefficientScale t a b h) =
      (PolygonScaledReciprocal.scaling b).comp
        ((leftLaurentMap t).comp (branchSwapMap t)) := by
  apply chartRing_hom_ext t
  · simp only [AlgHom.coe_comp, Function.comp_apply, twoCoefficientScale_left, map_mul,
      AlgHom.commutes, branchSwapMap_left, AddMonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self,
      RingHom.coe_id, id_eq, LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.T_zero,
      mul_one, leftLaurentMap_right, Int.reduceNeg, PolygonScaledReciprocal.scaling,
      AlgHom.coe_mk, PolygonChartScaling.laurent_C, PolygonChartScaling.laurent_T_neg_one]
    rw [← mul_assoc, ← map_mul, twoCoefficientScale_right_parameter t a b h]
    simp only [map_mul, mul_assoc, mul_left_comm]
  · simp [PolygonScaledReciprocal.scaling, AlgHom.coe_mk]

/-- The actual first puncture square commutes over the unchanged nonreduced base. -/
@[reassoc] theorem leftBranch_twoCoefficientScaling :
    leftBranchOpen R t ≫ (twoCoefficientScalingIso t a b h).hom =
      (edgeScalingIso a).hom ≫ leftBranchOpen R t := by
  rw [leftBranchOpen_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext
    (congrArg AlgHom.toRingHom (leftLaurentMap_twoCoefficientScale t a b h)))

/-- The same whole-chart automorphism gives the full second puncture square. -/
@[reassoc] theorem rightBranch_twoCoefficientScaling :
    rightBranchOpen R t ≫ (twoCoefficientScalingIso t a b h).hom =
      (edgeScalingIso b).hom ≫ rightBranchOpen R t := by
  rw [rightBranchOpen_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext
    (congrArg AlgHom.toRingHom (rightLaurentMap_twoCoefficientScale t a b h)))

/-- Both full branches preserve the original coefficient morphism. -/
@[reassoc] theorem twoCoefficientScalingIso_base :
    (twoCoefficientScalingIso t a b h).hom ≫ chartStructure R t = chartStructure R t := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (twoCoefficientScale t a b h).comp_algebraMap)

/-- The entire closed correction is the zero-parameter specialization of this construction. -/
theorem twoCoefficientScalingIso_zero (ht : t = 0) :
    twoCoefficientScalingIso t a b h = independentScalingIso t ht a b := by
  apply Iso.ext
  change Spec.map _ = Spec.map _
  exact congrArg Spec.map (CommRingCat.hom_ext
    (congrArg AlgHom.toRingHom (twoCoefficientScale_zero t a b ht)))

end FLT.Mazur.PolygonSmoothing
