/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearNormalForm
public import FLT.Mazur.WeierstrassSuccessiveXScaleOne

/-!
# The full first retained equation at depth zero

Scale one eliminates the original horizontal variable before the normal-form
comparison. Thus the complete first retained chart is the incidence-conic
equation, with two components instead of the positive-depth three-component chart.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassDividedDepth WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S s = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "q" => algebraMap R S
local notation "U" => rootShearCurve (W.map q) r
local notation "a" => WeierstrassCurve.a₁ U
local notation "c" => q b6
local notation "F" => FiberCoordinate a c

/-- The complete sheared scale-one retained equation becomes the incidence-conic equation. -/
def coefficientShearScaleOneFiberEquiv :
    Coordinate U (q s) (q π) (q b3) (q b4 - r * q b3) c ≃ₐ[S] F :=
  ((parameterEquiv U (q s) (q π) (q b3) (q b4 - r * q b3) c
    1 0 0 0 c hs hp h3 (by rw [h3, h4, mul_zero, sub_zero]) rfl).trans
      (scaleOneModificationEquiv U 0 0 0 c)).trans
    (fiberNormalEquiv a c U rfl (coefficientShear_a₂_zero W S r hr))

/-- Scale-one elimination transports all three original sheared coordinates. -/
theorem coefficientShearScaleOneFiberEquiv_coord (i : Fin 3) :
    coefficientShearScaleOneFiberEquiv W s π b3 b4 b6 S r hs hp h3 h4 hr
      (coord U (q s) (q π) (q b3) (q b4 - r * q b3) c i) =
        ![fiberT a c, fiberV a c,
          fiberV a c ^ 2 + algebraMap S F a * fiberV a c -
            algebraMap S F c * fiberT a c ^ 2] i := by
  rw [coefficientShearScaleOneFiberEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    parameterEquiv_coord, scaleOneModificationEquiv_coord]
  fin_cases i
  · exact fiberNormalEquiv_t a c U rfl (coefficientShear_a₂_zero W S r hr)
  · exact fiberNormalEquiv_v a c U rfl (coefficientShear_a₂_zero W S r hr)
  · change fiberNormalEquiv a c U rfl (coefficientShear_a₂_zero W S r hr)
      (WeierstrassModificationX.x U 0 0 0 c) =
        fiberV a c ^ 2 + algebraMap S F a * fiberV a c -
          algebraMap S F c * fiberT a c ^ 2
    simp only [WeierstrassModificationX.x, map_sub, map_add, map_mul, map_pow,
      AlgEquiv.commutes, fiberNormalEquiv_t, fiberNormalEquiv_v, map_zero,
      zero_mul, add_zero, coefficientShear_a₂_zero W S r hr, zero_add]

/-- The entire original first retained tensor chart has the depth-zero normal form. -/
def tensorShearScaleOneFiberEquiv : ScalarExtension W s π b3 b4 b6 S ≃ₐ[S] F :=
  (successiveCoefficientShearEquiv W s π b3 b4 b6 S r).trans
    (coefficientShearScaleOneFiberEquiv W s π b3 b4 b6 S r hs hp h3 h4 hr)

/-- Every original tensor coordinate survives, including the tangent-root shift. -/
theorem tensorShearScaleOneFiberEquiv_coord (i : Fin 3) :
    tensorShearScaleOneFiberEquiv W s π b3 b4 b6 S r hs hp h3 h4 hr
      (tensorCoord W s π b3 b4 b6 S i) =
        ![fiberT a c, fiberV a c + algebraMap S F r,
          fiberV a c ^ 2 + algebraMap S F a * fiberV a c -
            algebraMap S F c * fiberT a c ^ 2] i := by
  change coefficientShearScaleOneFiberEquiv W s π b3 b4 b6 S r hs hp h3 h4 hr
    (successiveCoefficientShearEquiv W s π b3 b4 b6 S r
      ((1 : S) ⊗ₜ[R] coord W s π b3 b4 b6 i)) = _
  rw [successiveCoefficientShearEquiv_tmul, one_smul, coefficientMap_coord,
    extendedCoord, shearForward_coord]
  fin_cases i <;> simp [coefficientShearScaleOneFiberEquiv_coord]

end FLT.Mazur.WeierstrassSuccessiveX
