/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTopNodeReduction
public import FLT.Mazur.PolygonSmoothingSpecialBranches
public import FLT.Mazur.LaurentCoefficientEvaluation

/-!
# Original node restrictions in every top parameter layer

A top-weighted node function depends only on its actual split-node
reduction. Its Laurent restriction is the top weight times the original
polynomial branch, retaining every coefficient over nonreduced base rings.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial PolygonScalingNaturality LaurentCoefficientEvaluation
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R] (m : ℕ)
local notation "S" => Ring R (m + 1)
local notation "e" => parameter R (m + 1)
local notation "B" => ChartRing (e)

/-- A top-weighted scalar depends only on its original closed-fiber value. -/
theorem topParameter_mul_reduction (s : S) :
    (e) ^ (m + 1) * s = (e) ^ (m + 1) * algebraMap R (S) (reduction R (m + 1) s) := by
  apply sub_eq_zero.mp
  rw [← mul_sub]
  have hz : reduction R (m + 1) (s - algebraMap R (S) (reduction R (m + 1) s)) = 0 := by
    rw [map_sub (reduction R (m + 1)), (reduction R (m + 1)).commutes,
      Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  exact (parameter_last_mul_eq_zero_iff R m _).mpr hz

/-- The same exact formula holds coefficientwise on the whole Laurent ring. -/
theorem topLaurent_parameter_reduction (p : (S)[T;T⁻¹]) :
    C ((e) ^ (m + 1)) * p = C ((e) ^ (m + 1)) * coeffMap (algebraMap R (S))
      (coeffMap (reduction R (m + 1)).toRingHom p) := by
  ext d
  simp only [← smul_eq_C_mul, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, coeffMap_coeff]
  exact topParameter_mul_reduction R m (p.coeff d)

/-- The original positive-stage node reduction commutes with restriction to its Laurent edge. -/
theorem topNodeReduction_leftLaurent (z : B) :
    coeffMap (reduction R (m + 1)).toRingHom (leftLaurentMap (e) z) =
      leftLaurentMap (0 : R) (topNodeReduction R m z) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  induction p using MvPolynomial.induction_on with
  | C s =>
    change coeffMap (reduction R (m + 1)).toRingHom
      (leftLaurentMap (e) (algebraMap (S) (B) s)) =
      leftLaurentMap (0 : R) (topNodeReduction R m (algebraMap (S) (B) s))
    rw [AlgHom.commutes, topNodeReduction, ringMap_scalar, AlgHom.commutes]
    exact coeffMap_C _ s
  | add p q hp hq =>
    simp only [(topNodeReduction R m).map_add, map_add, hp, hq]
  | mul_X p i hp =>
    have hc : coeffMap (reduction R (m + 1)).toRingHom
        (leftLaurentMap (e) (Ideal.Quotient.mk _ (MvPolynomial.X i))) =
        leftLaurentMap (0 : R)
          (topNodeReduction R m (Ideal.Quotient.mk _ (MvPolynomial.X i))) := by
      fin_cases i
      · change coeffMap (reduction R (m + 1)).toRingHom
          (leftLaurentMap (e) (leftCoordinate (e))) =
          leftLaurentMap (0 : R) (topNodeReduction R m (leftCoordinate (e)))
        rw [leftLaurentMap_left, coeffMap_T, topNodeReduction_left, leftLaurentMap_left]
      · change coeffMap (reduction R (m + 1)).toRingHom
          (leftLaurentMap (e) (rightCoordinate (e))) =
          leftLaurentMap (0 : R) (topNodeReduction R m (rightCoordinate (e)))
        rw [leftLaurentMap_right, map_mul, coeffMap_C,
          show (reduction R (m + 1)).toRingHom (e) = 0 from reduction_parameter R (m + 1),
          map_zero, zero_mul, topNodeReduction_right, leftLaurentMap_right, map_zero,
          zero_mul]
    simp only [(topNodeReduction R m).map_mul, map_mul, hp, hc]

/-- Weighting a node function by the top power keeps exactly its special-fiber branch polynomial. -/
theorem topNode_parameter_leftLaurent (z : B) :
    C ((e) ^ (m + 1)) * leftLaurentMap (e) z = C ((e) ^ (m + 1)) * coeffMap (algebraMap R (S))
      (Polynomial.toLaurent (PolygonNodeEqualizer.first
        (specialFiberEquiv R (topNodeReduction R m z)))) := by
  rw [topLaurent_parameter_reduction, topNodeReduction_leftLaurent]
  exact congrArg (fun p ↦ C ((e) ^ (m + 1)) * coeffMap (algebraMap R (S)) p)
    (AlgHom.congr_fun (specialLeftMap_comparison R) (topNodeReduction R m z)).symm

end FLT.Mazur.PolygonInfinitesimalStages
