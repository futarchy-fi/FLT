/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXScaleOneEquiv
public import FLT.Mazur.WeierstrassModificationXBaseChangeGenerators

/-!
# Scale-one slope comparison of the original tensor algebra

The entire tensor chart is identified with the slope localization when its
specialized scale is one and its other coefficients vanish. Every original
incidence, slope and cubic function is transported through the same comparison.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (S : Type*) [CommRing S] [Algebra R S]
  (hs : algebraMap R S s = 1) (h2 : algebraMap R S W.a₂ = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (h6 : algebraMap R S b6 = 0)
local notation "a" => algebraMap R S W.a₁

/-- Specializing scale to one identifies the entire original tensor chart. -/
def scaleOneTensorEquiv : ScalarExtension W s b3 b4 b6 S ≃ₐ[S] SlopeOpen a :=
  (baseChangeEquiv W s b3 b4 b6 S).trans
    (scaleOneSlopeEquiv (W.map (algebraMap R S)) (algebraMap R S s)
      (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6) hs h2 h3 h4 h6)

/-- The actual original incidence tensor is the inverse of the whole tangent product. -/
theorem scaleOneTensorEquiv_t :
    scaleOneTensorEquiv W s b3 b4 b6 S hs h2 h3 h4 h6
      ((1 : S) ⊗ₜ[R] t W s b3 b4 b6) = slopeInv a := by
  rw [scaleOneTensorEquiv, AlgEquiv.trans_apply, baseChangeEquiv_t]
  exact scaleOneSlopeEquiv_t (W.map (algebraMap R S)) (algebraMap R S s)
    (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6) hs h2 h3 h4 h6

/-- The actual original slope tensor is the polynomial parameter. -/
theorem scaleOneTensorEquiv_v :
    scaleOneTensorEquiv W s b3 b4 b6 S hs h2 h3 h4 h6
      ((1 : S) ⊗ₜ[R] v W s b3 b4 b6) = slopeZ a := by
  rw [scaleOneTensorEquiv, AlgEquiv.trans_apply, baseChangeEquiv_v]
  exact scaleOneSlopeEquiv_v (W.map (algebraMap R S)) (algebraMap R S s)
    (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6) hs h2 h3 h4 h6

omit hs h2 h3 h4 h6 in
/-- Coefficient extension preserves the recovered original cubic horizontal function. -/
theorem coefficientMap_x :
    coefficientMap W s b3 b4 b6 S (x W s b3 b4 b6) =
      x (W.map (algebraMap R S)) (algebraMap R S s)
        (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6) := by
  simp only [x, map_add, map_sub, map_mul, map_pow, AlgHom.commutes,
    coefficientMap_t, coefficientMap_v, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    ← IsScalarTower.algebraMap_apply R S]

/-- The entire comparison retains the original horizontal cubic function. -/
theorem scaleOneTensorEquiv_x :
    scaleOneTensorEquiv W s b3 b4 b6 S hs h2 h3 h4 h6
      ((1 : S) ⊗ₜ[R] x W s b3 b4 b6) =
        slopeZ a * (slopeZ a + algebraMap S (SlopeOpen a) a) := by
  rw [scaleOneTensorEquiv, AlgEquiv.trans_apply, baseChangeEquiv_tmul, one_smul,
    coefficientMap_x]
  exact scaleOneSlopeEquiv_x (W.map (algebraMap R S)) (algebraMap R S s)
    (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6) hs h2 h3 h4 h6

/-- The entire comparison retains the original vertical cubic function. -/
theorem scaleOneTensorEquiv_y :
    scaleOneTensorEquiv W s b3 b4 b6 S hs h2 h3 h4 h6
      ((1 : S) ⊗ₜ[R] y W s b3 b4 b6) =
        (slopeZ a * (slopeZ a + algebraMap S (SlopeOpen a) a)) * slopeZ a := by
  have h : (1 : S) ⊗ₜ[R] y W s b3 b4 b6 =
      ((1 : S) ⊗ₜ[R] x W s b3 b4 b6) * ((1 : S) ⊗ₜ[R] v W s b3 b4 b6) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, y]
  rw [h, map_mul, scaleOneTensorEquiv_x, scaleOneTensorEquiv_v]

end FLT.Mazur.WeierstrassModificationX
