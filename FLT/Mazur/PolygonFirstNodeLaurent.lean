/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstNodeReduction
public import FLT.Mazur.PolygonSmoothingSpecialBranches
public import FLT.Mazur.LaurentCoefficientEvaluation

/-!
# First-order node restrictions retain their reduced polynomial coefficient

Multiplication by the smoothing parameter kills precisely the reduction
kernel. On the Laurent edge this gives a coefficientwise formula, which
identifies the correction of a node coordinate with its polynomial branch
restriction on the original special fiber.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial PolygonScalingNaturality LaurentCoefficientEvaluation
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R]
local notation "S" => Ring R 1
local notation "e" => parameter R 1
local notation "B" => ChartRing (e)

/-- A parameter-weighted scalar depends only on its original closed-fiber value. -/
theorem firstParameter_mul_reduction (s : S) :
    (e) * s = (e) * algebraMap R (S) (reduction R 1 s) := by
  apply sub_eq_zero.mp
  rw [← mul_sub]
  have hz : reduction R 1 (s - algebraMap R (S) (reduction R 1 s)) = 0 := by
    rw [map_sub (reduction R 1), (reduction R 1).commutes,
      Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  simpa only [Nat.zero_add, pow_one] using
    (parameter_last_mul_eq_zero_iff R 0 _).mpr hz

/-- The same exact formula holds coefficientwise on the whole Laurent ring. -/
theorem firstLaurent_parameter_reduction (p : (S)[T;T⁻¹]) :
    C (e) * p = C (e) * coeffMap (algebraMap R (S))
      (coeffMap (reduction R 1).toRingHom p) := by
  ext d
  simp only [← smul_eq_C_mul, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, coeffMap_coeff]
  exact firstParameter_mul_reduction R (p.coeff d)

/-- The original first node reduction commutes with restriction to its Laurent edge. -/
theorem firstNodeReduction_leftLaurent (z : B) :
    coeffMap (reduction R 1).toRingHom (leftLaurentMap (e) z) =
      leftLaurentMap (0 : R) (firstNodeReduction R z) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  induction p using MvPolynomial.induction_on with
  | C s =>
    change coeffMap (reduction R 1).toRingHom
      (leftLaurentMap (e) (algebraMap (S) (B) s)) =
      leftLaurentMap (0 : R) (firstNodeReduction R (algebraMap (S) (B) s))
    rw [AlgHom.commutes, firstNodeReduction, ringMap_scalar, AlgHom.commutes]
    exact coeffMap_C _ s
  | add p q hp hq =>
    simp only [(firstNodeReduction R).map_add, map_add, hp, hq]
  | mul_X p i hp =>
    have hc : coeffMap (reduction R 1).toRingHom
        (leftLaurentMap (e) (Ideal.Quotient.mk _ (MvPolynomial.X i))) =
        leftLaurentMap (0 : R)
          (firstNodeReduction R (Ideal.Quotient.mk _ (MvPolynomial.X i))) := by
      fin_cases i
      · change coeffMap (reduction R 1).toRingHom
          (leftLaurentMap (e) (leftCoordinate (e))) =
          leftLaurentMap (0 : R) (firstNodeReduction R (leftCoordinate (e)))
        rw [leftLaurentMap_left, coeffMap_T, firstNodeReduction_left, leftLaurentMap_left]
      · change coeffMap (reduction R 1).toRingHom
          (leftLaurentMap (e) (rightCoordinate (e))) =
          leftLaurentMap (0 : R) (firstNodeReduction R (rightCoordinate (e)))
        rw [leftLaurentMap_right, map_mul, coeffMap_C,
          show (reduction R 1).toRingHom (e) = 0 from reduction_parameter R 1,
          map_zero, zero_mul, firstNodeReduction_right, leftLaurentMap_right, map_zero,
          zero_mul]
    simp only [(firstNodeReduction R).map_mul, map_mul, hp, hc]

/-- Weighting a node function by the parameter keeps exactly its special-fiber branch polynomial. -/
theorem firstNode_parameter_leftLaurent (z : B) :
    C (e) * leftLaurentMap (e) z = C (e) * coeffMap (algebraMap R (S))
      (Polynomial.toLaurent (PolygonNodeEqualizer.first
        (specialFiberEquiv R (firstNodeReduction R z)))) := by
  rw [firstLaurent_parameter_reduction, firstNodeReduction_leftLaurent]
  exact congrArg (fun p ↦ C (e) * coeffMap (algebraMap R (S)) p)
    (AlgHom.congr_fun (specialLeftMap_comparison R) (firstNodeReduction R z)).symm

end FLT.Mazur.PolygonInfinitesimalStages
