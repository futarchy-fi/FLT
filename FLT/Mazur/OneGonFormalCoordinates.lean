/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PowerSeriesSubstitutionEquiv
public import Mathlib.Tactic.LinearCombination

/-!
# Formal normal form of the one-gon cubic

The inverse of `t² - t` at zero separates the two branches in every
characteristic. A shear, an invertible univariate substitution, and a
linear change of coordinates carry the cubic to `xy`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.OneGonFormalCoordinates
variable (K : Type*) [CommRing K]
open PowerSeriesSubstitutionEquiv

/-- The branch parameter solving t² - t = u at t = 0. -/
def root : PowerSeries K :=
  (PowerSeries.X ^ 2 - PowerSeries.X : PowerSeries K).substInvOfIsUnit
    (by simp)
@[simp] theorem root_zero : (root K).constantCoeff = 0 :=
  PowerSeries.constantCoeff_substInvOfIsUnit _ _
theorem root_relation : root K ^ 2 - root K = PowerSeries.X := by
  have ht : PowerSeries.HasSubst (root K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (root_zero K)
  have h := PowerSeries.subst_substInvOfIsUnit_right
    (PowerSeries.X ^ 2 - PowerSeries.X : PowerSeries K) (by simp)
    (show IsUnit ((PowerSeries.coeff 1) (PowerSeries.X ^ 2 - PowerSeries.X : PowerSeries K))
      from by simp)
  change (PowerSeries.X ^ 2 - PowerSeries.X : PowerSeries K).subst (root K) = _ at h
  simpa only [PowerSeries.subst_sub ht, PowerSeries.subst_pow ht,
    PowerSeries.subst_X ht] using h

/-- The shift of the second coordinate along the branch through zero. -/
def shift : PowerSeries K := PowerSeries.X * root K
@[simp] theorem shift_zero : (shift K).constantCoeff = 0 := by simp [shift]
/-- The difference of the two tangent branches, with linear coefficient -1. -/
def difference : PowerSeries K := PowerSeries.X * (2 * root K - 1)
@[simp] theorem difference_zero : (difference K).constantCoeff = 0 := by simp [difference]
@[simp] theorem difference_one : (difference K).coeff 1 = -1 := by
  simp [difference]
/-- The inverse parameter for the difference of the branches. -/
def inverse : PowerSeries K := (difference K).substInvOfIsUnit (by simp)
@[simp] theorem inverse_zero : (inverse K).constantCoeff = 0 :=
  PowerSeries.constantCoeff_substInvOfIsUnit _ _
theorem inverse_one : IsUnit ((inverse K).coeff 1) := by
  rw [inverse, PowerSeries.coeff_one_substInvOfIsUnit]
  exact Units.isUnit _
theorem difference_inverse : (difference K).subst (inverse K) = PowerSeries.X :=
  PowerSeries.subst_substInvOfIsUnit_right _ (difference_zero K) _

open MvPowerSeries
/-- The formal cubic defining the one-gon chart. -/
def cubic : MvPowerSeries (Fin 2) K := X 1 ^ 2 - X 0 * X 1 - X 0 ^ 3

theorem shear_cubic : shear (shift K) (shift_zero K) (cubic K) =
    X 1 * (X 1 + (difference K).subst (X 0)) := by
  have ht := congrArg (PowerSeries.substAlgHom
    (PowerSeries.HasSubst.X (S := K) (0 : Fin 2))) (root_relation K)
  simp only [map_sub, map_pow, PowerSeries.substAlgHom_X] at ht
  simp only [cubic, map_sub, map_pow, map_mul, shear_X_zero, shear_X_one]
  rw [← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.X (S := K) (0 : Fin 2))]
  simp only [shift, difference, map_mul, map_sub, map_ofNat, map_one,
    PowerSeries.substAlgHom_X]
  linear_combination (X 0 : MvPowerSeries (Fin 2) K) ^ 2 * ht

/-- Formal coordinates that turn the cubic into the product of the coordinates. -/
def equivalence : MvPowerSeries (Fin 2) K ≃ₐ[K] MvPowerSeries (Fin 2) K :=
  ((shear (shift K) (shift_zero K)).trans
    (firstCoordinate (inverse K) (inverse_zero K) (inverse_one K))).trans subtractSecond

theorem equation : equivalence K (cubic K) = X 0 * X 1 := by
  simp only [equivalence, AlgEquiv.trans_apply, shear_cubic, map_mul, map_add,
    firstCoordinate_X_one, firstCoordinate_univariate]
  rw [← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (inverse_zero K))
    (PowerSeries.HasSubst.X (S := K) (0 : Fin 2)), difference_inverse,
    PowerSeries.subst_X (PowerSeries.HasSubst.X (S := K) (0 : Fin 2))]
  simp only [subtractSecond_X_one, subtractSecond_X_zero]
  ring
end FLT.Mazur.OneGonFormalCoordinates
