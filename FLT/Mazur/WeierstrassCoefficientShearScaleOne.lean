/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIncidenceShearNormalForm
public import FLT.Mazur.WeierstrassModificationXScaleOneTensor

/-!
# The full depth-zero incidence equation after the actual tangent shear

At scale one the whole incidence chart is the slope line with both tangent
factors inverted. The tensor comparison keeps the original root shift and
both original cubic functions, without a positive-depth assumption.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (S : Type*) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S s = 1) (h3 : algebraMap R S b3 = 0)
  (h4 : algebraMap R S b4 = 0) (h6 : algebraMap R S b6 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "q" => algebraMap R S
local notation "U" => rootShearCurve (W.map q) r
local notation "a" => WeierstrassCurve.a₁ U
local notation "P" => SlopeOpen a

/-- The complete sheared scale-one equation is the full slope localization. -/
def coefficientShearScaleOneEquiv :
    Coordinate U (q s) (q b3) (q b4 - r * q b3) (q b6) ≃ₐ[S] P :=
  scaleOneSlopeEquiv U (q s) (q b3) (q b4 - r * q b3) (q b6) hs
    (coefficientShear_a₂_zero W S r hr) h3 (by rw [h3, h4, mul_zero, sub_zero]) h6

/-- The original tensor incidence chart at scale one retains the actual tangent shear. -/
def tensorShearScaleOneEquiv : ScalarExtension W s b3 b4 b6 S ≃ₐ[S] P :=
  (incidenceCoefficientShearEquiv W s b3 b4 b6 S r).trans
    (coefficientShearScaleOneEquiv W s b3 b4 b6 S r hs h3 h4 h6 hr)

/-- The original incidence is the inverse of the full sheared tangent product. -/
theorem tensorShearScaleOneEquiv_t :
    tensorShearScaleOneEquiv W s b3 b4 b6 S r hs h3 h4 h6 hr
      ((1 : S) ⊗ₜ[R] t W s b3 b4 b6) = slopeInv a := by
  change coefficientShearScaleOneEquiv W s b3 b4 b6 S r hs h3 h4 h6 hr
    (incidenceCoefficientShearEquiv W s b3 b4 b6 S r _) = _
  rw [incidenceCoefficientShearEquiv_t]
  exact scaleOneSlopeEquiv_t _ _ _ _ _ _ _ _ _ _

/-- The original tangent slope keeps its root shift on the entire depth-zero chart. -/
theorem tensorShearScaleOneEquiv_v :
    tensorShearScaleOneEquiv W s b3 b4 b6 S r hs h3 h4 h6 hr
      ((1 : S) ⊗ₜ[R] v W s b3 b4 b6) = slopeZ a + algebraMap S P r := by
  change coefficientShearScaleOneEquiv W s b3 b4 b6 S r hs h3 h4 h6 hr
    (incidenceCoefficientShearEquiv W s b3 b4 b6 S r _) = _
  rw [incidenceCoefficientShearEquiv_v, map_add, AlgEquiv.commutes]
  rw [coefficientShearScaleOneEquiv, scaleOneSlopeEquiv_v]

/-- Shearing fixes the original horizontal cubic function. -/
theorem tensorShearScaleOneEquiv_x :
    tensorShearScaleOneEquiv W s b3 b4 b6 S r hs h3 h4 h6 hr
      ((1 : S) ⊗ₜ[R] x W s b3 b4 b6) =
        slopeZ a * (slopeZ a + algebraMap S P a) := by
  change coefficientShearScaleOneEquiv W s b3 b4 b6 S r hs h3 h4 h6 hr
    (incidenceCoefficientShearEquiv W s b3 b4 b6 S r _) = _
  rw [incidenceCoefficientShearEquiv_tmul, one_smul, coefficientMap_x, shearForward_x]
  exact scaleOneSlopeEquiv_x _ _ _ _ _ _ _ _ _ _

/-- The original vertical cubic function retains the chosen tangent root. -/
theorem tensorShearScaleOneEquiv_y :
    tensorShearScaleOneEquiv W s b3 b4 b6 S r hs h3 h4 h6 hr
      ((1 : S) ⊗ₜ[R] y W s b3 b4 b6) =
        (slopeZ a * (slopeZ a + algebraMap S P a)) *
          (slopeZ a + algebraMap S P r) := by
  have h : (1 : S) ⊗ₜ[R] y W s b3 b4 b6 =
      ((1 : S) ⊗ₜ[R] x W s b3 b4 b6) * ((1 : S) ⊗ₜ[R] v W s b3 b4 b6) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, y]
  rw [h, map_mul, tensorShearScaleOneEquiv_x, tensorShearScaleOneEquiv_v]

end FLT.Mazur.WeierstrassModificationX
