/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXConicBoundaryCoordinates
public import FLT.Mazur.WeierstrassModificationXConicZeroParameters
public import Mathlib.Algebra.Polynomial.Laurent

/-!
# Ordered punctured parameters on a zero-constant retained conic

The first conic parameter has t=a₁*z and v=0; the second has t=-a₁*z
and v=-a₁. Inverting z gives actual maps from the original incidence open,
with the reciprocal tangent ratios needed for the next node chart.
-/

@[expose] public noncomputable section
open LaurentPolynomial
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (c : R)
  (ha : IsUnit W.a₁) (hc : c = 0)
local notation "C₀" => ConicCoordinate W.a₁ c
local notation "B" => MiddleConicOpen W c
local notation "L" => R[T;T⁻¹]
local notation "u" => conicBoundaryUnit W c

/-- The first ordered parameter on the full original conic, restricted to its puncture. -/
def conicPuncturedFirst : C₀ →ₐ[R] L :=
  conicEvaluation W.a₁ c (C W.a₁ * T 1) 0 (by rw [hc]; simp)

/-- The second ordered parameter retains the opposite slope and its original sign. -/
def conicPuncturedSecond : C₀ →ₐ[R] L :=
  conicEvaluation W.a₁ c (-C W.a₁ * T 1) (-C W.a₁) (by rw [hc]; simp)

/-- The first punctured parameter inverts the actual incidence function. -/
def conicBoundaryFirst : B →ₐ[R] L :=
  IsLocalization.Away.liftAlgHom (f := conicPuncturedFirst W c hc) (conicT W.a₁ c) (by
    change IsUnit (conicEvaluation _ _ _ _ _ (conicT _ _))
    rw [conicEvaluation_t]
    exact (ha.map C).mul (isUnit_T 1))

/-- The second punctured parameter also inverts the actual incidence function. -/
def conicBoundarySecond : B →ₐ[R] L :=
  IsLocalization.Away.liftAlgHom (f := conicPuncturedSecond W c hc) (conicT W.a₁ c) (by
    change IsUnit (conicEvaluation _ _ _ _ _ (conicT _ _))
    rw [conicEvaluation_t]
    exact (ha.map C).neg.mul (isUnit_T 1))

/-- The first boundary lift retains every original conic function. -/
theorem conicBoundaryFirst_base (q : C₀) :
    conicBoundaryFirst W c ha hc (algebraMap C₀ B q) = conicPuncturedFirst W c hc q := by
  rw [conicBoundaryFirst, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- The second boundary lift retains every original conic function. -/
theorem conicBoundarySecond_base (q : C₀) :
    conicBoundarySecond W c ha hc (algebraMap C₀ B q) = conicPuncturedSecond W c hc q := by
  rw [conicBoundarySecond, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- The first parameter's original slope is zero. -/
theorem conicBoundaryFirst_v :
    conicBoundaryFirst W c ha hc (algebraMap C₀ B (conicV W.a₁ c)) = 0 := by
  rw [conicBoundaryFirst_base]
  exact conicEvaluation_v ..

/-- The second parameter's original slope is minus the tangent coefficient. -/
theorem conicBoundarySecond_v :
    conicBoundarySecond W c ha hc (algebraMap C₀ B (conicV W.a₁ c)) = -C W.a₁ := by
  rw [conicBoundarySecond_base]
  exact conicEvaluation_v ..

/-- The incidence unit is a₁ times the first parameter. -/
theorem conicBoundaryFirst_unit : conicBoundaryFirst W c ha hc (↑u : B) = C W.a₁ * T 1 := by
  rw [conicBoundaryUnit_val, conicBoundaryFirst_base]
  exact conicEvaluation_t ..

/-- The incidence unit is -a₁ times the second parameter. -/
theorem conicBoundarySecond_unit :
    conicBoundarySecond W c ha hc (↑u : B) = -C W.a₁ * T 1 := by
  rw [conicBoundaryUnit_val, conicBoundarySecond_base]
  exact conicEvaluation_t ..

/-- On the first branch the opposite tangent ratio is the reciprocal parameter. -/
theorem conicBoundaryFirst_inverse_mul :
    conicBoundaryFirst W c ha hc (↑u⁻¹ : B) * C W.a₁ = T (-1) := by
  apply (isUnit_T (R := R) 1).mul_left_inj.mp
  rw [mul_assoc, ← conicBoundaryFirst_unit W c ha hc, ← map_mul, Units.inv_mul, map_one]
  simp only [← T_add, neg_add_cancel, T_zero]

/-- On the second branch the first tangent ratio is the reciprocal parameter. -/
theorem conicBoundarySecond_inverse_mul :
    conicBoundarySecond W c ha hc (↑u⁻¹ : B) * (-C W.a₁) = T (-1) := by
  apply (isUnit_T (R := R) 1).mul_left_inj.mp
  rw [mul_assoc, ← conicBoundarySecond_unit W c ha hc, ← map_mul, Units.inv_mul, map_one]
  simp only [← T_add, neg_add_cancel, T_zero]

end FLT.Mazur.WeierstrassSuccessiveX
