/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCoefficientShear
public import FLT.Mazur.WeierstrassModificationXFiberNormalForm

/-!
# The full incidence equation after a coefficient tangent shear

Vanishing of the scale and divided linear coefficients identifies the actual
sheared equation with the incidence line and conic equation. The original slope
is the normal slope plus the chosen root; the constant coefficient is retained.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {S : Type*} [CommRing S] (U : WeierstrassCurve S) (s b3 b4 c : S)
  (hs : s = 0) (h3 : b3 = 0) (h4 : b4 = 0) (h2 : U.a₂ = 0)

/-- The full incidence equation with vanishing linear data, keeping its conic constant. -/
def zeroLinearNormalEquiv : Coordinate U s b3 b4 c ≃ₐ[S] FiberCoordinate U.a₁ c := by
  subst s b3 b4
  exact fiberNormalEquiv U.a₁ c U rfl h2

/-- The normal comparison fixes incidence, including its zero locus. -/
theorem zeroLinearNormalEquiv_t :
    zeroLinearNormalEquiv U s b3 b4 c hs h3 h4 h2 (t U s b3 b4 c) = fiberT U.a₁ c := by
  subst s b3 b4
  exact fiberNormalEquiv_t U.a₁ c U rfl h2

/-- The normal comparison fixes the entire slope function. -/
theorem zeroLinearNormalEquiv_v :
    zeroLinearNormalEquiv U s b3 b4 c hs h3 h4 h2 (v U s b3 b4 c) = fiberV U.a₁ c := by
  subst s b3 b4
  exact fiberNormalEquiv_v U.a₁ c U rfl h2

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (S : Type*) [CommRing S] [Algebra R S] (r : S)
local notation "q" => algebraMap R S
local notation "U" => rootShearCurve (W.map q) r
local notation "a" => WeierstrassCurve.a₁ U
local notation "c" => q b6
variable (hs : algebraMap R S s = 0) (h3 : algebraMap R S b3 = 0)
  (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)

include hr in
/-- A root of the actual tangent polynomial kills the quadratic shear coefficient. -/
theorem coefficientShear_a₂_zero : (U).a₂ = 0 := by
  rw [(rootShearCurve_coefficients r).2.1]
  change q W.a₂ - r * q W.a₁ - r ^ 2 = 0
  linear_combination -hr

/-- The entire sheared coefficient equation has the full incidence-conic normal form. -/
def coefficientShearNormalEquiv :
    Coordinate U (q s) (q b3) (q b4 - r * q b3) c ≃ₐ[S] FiberCoordinate a c :=
  zeroLinearNormalEquiv U (q s) (q b3) (q b4 - r * q b3) c hs h3
    (by rw [h3, h4, mul_zero, sub_zero]) (coefficientShear_a₂_zero W S r hr)

/-- Incidence is retained by the full sheared equation comparison. -/
theorem coefficientShearNormalEquiv_t :
    coefficientShearNormalEquiv W s b3 b4 b6 S r hs h3 h4 hr
      (t U (q s) (q b3) (q b4 - r * q b3) c) = fiberT a c :=
  zeroLinearNormalEquiv_t U (q s) (q b3) (q b4 - r * q b3) c _ _ _ _

/-- The sheared slope is retained on the conic as well as on the incidence line. -/
theorem coefficientShearNormalEquiv_v :
    coefficientShearNormalEquiv W s b3 b4 b6 S r hs h3 h4 hr
      (v U (q s) (q b3) (q b4 - r * q b3) c) = fiberV a c :=
  zeroLinearNormalEquiv_v U (q s) (q b3) (q b4 - r * q b3) c _ _ _ _

/-- The original tensor incidence equation, without removing any exceptional component. -/
def tensorShearNormalEquiv : ScalarExtension W s b3 b4 b6 S ≃ₐ[S] FiberCoordinate a c :=
  (incidenceCoefficientShearEquiv W s b3 b4 b6 S r).trans
    (coefficientShearNormalEquiv W s b3 b4 b6 S r hs h3 h4 hr)

/-- The original tensor incidence is exactly the normal incidence parameter. -/
theorem tensorShearNormalEquiv_t :
    tensorShearNormalEquiv W s b3 b4 b6 S r hs h3 h4 hr
      ((1 : S) ⊗ₜ[R] t W s b3 b4 b6) = fiberT a c := by
  change coefficientShearNormalEquiv W s b3 b4 b6 S r hs h3 h4 hr
    (incidenceCoefficientShearEquiv W s b3 b4 b6 S r _) = _
  rw [incidenceCoefficientShearEquiv_t, coefficientShearNormalEquiv_t]

/-- The original slope keeps the root shift on the whole special fiber. -/
theorem tensorShearNormalEquiv_v :
    tensorShearNormalEquiv W s b3 b4 b6 S r hs h3 h4 hr
      ((1 : S) ⊗ₜ[R] v W s b3 b4 b6) = fiberV a c + algebraMap S _ r := by
  change coefficientShearNormalEquiv W s b3 b4 b6 S r hs h3 h4 hr
    (incidenceCoefficientShearEquiv W s b3 b4 b6 S r _) = _
  rw [incidenceCoefficientShearEquiv_v, map_add, coefficientShearNormalEquiv_v,
    AlgEquiv.commutes]

end FLT.Mazur.WeierstrassModificationX
