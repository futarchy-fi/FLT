/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentNormalizationChart

/-!
# Actual semilinear conjugation on the root-sheared normalization chart

The adjoined root goes to s-a and the normalization coordinate goes to
z+a. Both original cubic coordinates are fixed. The resulting involution
intertwines the actual tensor coefficient operation on every chart function.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur
open Polynomial WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "s" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "a" => WeierstrassCurve.a₁ (nodeTangentShear W)
local notation "σ" => nodeTangentConjugation W

/-- The actual root exchange negates the transverse coefficient of the sheared model. -/
theorem nodeTangentShear_a₁_conjugate : σ a = -a := by
  rw [(nodeTangentShear_coefficients W).1]
  simp only [map_add, map_mul, map_ofNat, AlgEquiv.commutes]
  rw [show σ s = -algebraMap R S W.a₁ - s from nodeTangentConjugationHom_root W]
  ring

/-- The normalization coordinate compensates for the actual root exchange by z ↦ z+a. -/
def nodeTangentNormalizationConjugation : S[X] →ₐ[R] S[X] where
  toRingHom := eval₂RingHom (C.comp (σ).toRingHom) (X + C a)
  commutes' r := by
    change eval₂ (C.comp (σ).toRingHom) (X + C a) (C (algebraMap R S r)) = _
    rw [eval₂_C]
    change C (σ (algebraMap R S r)) = C (algebraMap R S r)
    rw [AlgEquiv.commutes]

@[simp] theorem nodeTangentNormalizationConjugation_C (c : S) :
    nodeTangentNormalizationConjugation W (C c) = C (σ c) := eval₂_C _ _

@[simp] theorem nodeTangentNormalizationConjugation_X :
    nodeTangentNormalizationConjugation W X = X + C a := eval₂_X _ _

/-- The compensating coordinate shift and coefficient conjugation together are involutive. -/
theorem nodeTangentNormalizationConjugation_involutive :
    Function.Involutive (nodeTangentNormalizationConjugation W) := by
  have he : (nodeTangentNormalizationConjugation W).comp
      (nodeTangentNormalizationConjugation W) = AlgHom.id R S[X] := by
    apply AlgHom.coe_ringHom_injective
    apply Polynomial.ringHom_ext
    · intro c
      change nodeTangentNormalizationConjugation W
        (nodeTangentNormalizationConjugation W (C c)) = C c
      rw [nodeTangentNormalizationConjugation_C, nodeTangentNormalizationConjugation_C]
      exact congrArg C (nodeTangentConjugationHom_involutive W c)
    · change nodeTangentNormalizationConjugation W
        (nodeTangentNormalizationConjugation W X) = X
      simp only [nodeTangentNormalizationConjugation_X, map_add,
        nodeTangentNormalizationConjugation_C, nodeTangentShear_a₁_conjugate, map_neg]
      ring
  intro z
  exact DFunLike.congr_fun he z

/-- The semilinear operation fixes the original unsheared x coordinate. -/
@[simp] theorem nodeTangentNormalizationConjugation_originalX :
    nodeTangentNormalizationConjugation W (nodeTangentNormalizationX W) =
      nodeTangentNormalizationX W := by
  simp only [nodeTangentNormalizationX, map_mul, map_add,
    nodeTangentNormalizationConjugation_X, nodeTangentNormalizationConjugation_C,
    nodeTangentShear_a₁_conjugate, map_neg]
  ring

/-- The compensating shift also fixes precisely the original unsheared y coordinate. -/
@[simp] theorem nodeTangentNormalizationConjugation_originalY :
    nodeTangentNormalizationConjugation W (nodeTangentNormalizationY W) =
      nodeTangentNormalizationY W := by
  simp only [nodeTangentNormalizationY, map_mul, map_add,
    nodeTangentNormalizationConjugation_X, nodeTangentNormalizationConjugation_C,
    nodeTangentNormalizationConjugation_originalX]
  rw [show σ s = -algebraMap R S W.a₁ - s from nodeTangentConjugationHom_root W,
    (nodeTangentShear_coefficients W).1]
  simp only [map_sub, map_neg, map_add, map_mul, map_ofNat]
  ring

/-- Every function on the original nodal chart, not only the displayed coordinates, is fixed. -/
theorem nodeTangentNormalizationConjugation_chart
    (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0) :
    (nodeTangentNormalizationConjugation W).comp
        (nodeTangentNormalizationChart W h₃ h₄ h₆) =
      nodeTangentNormalizationChart W h₃ h₄ h₆ := by
  apply hom_ext
  intro i
  fin_cases i <;> simp

/-- The normalization comparison intertwines actual coefficient conjugation on the tensor chart. -/
theorem nodeTangentNormalizationConjugation_tensor
    (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0) :
    (nodeTangentNormalizationConjugation W).comp
        (nodeTangentNormalizationTensor W h₃ h₄ h₆) =
      (nodeTangentNormalizationTensor W h₃ h₄ h₆).comp
        (TensorCoefficientSymmetry.equiv (A := Coordinate W 2) σ).toAlgHom := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul c b =>
    have hb := DFunLike.congr_fun (nodeTangentNormalizationConjugation_chart W h₃ h₄ h₆) b
    change nodeTangentNormalizationConjugation W
      (nodeTangentNormalizationTensor W h₃ h₄ h₆ (c ⊗ₜ[R] b)) =
      nodeTangentNormalizationTensor W h₃ h₄ h₆
        (TensorCoefficientSymmetry.equiv (A := Coordinate W 2) σ (c ⊗ₜ[R] b))
    rw [TensorCoefficientSymmetry.equiv_tmul]
    simpa only [AlgHom.comp_apply, nodeTangentNormalizationTensor_tmul, map_mul,
      nodeTangentNormalizationConjugation_C] using congrArg (C (σ c) * ·) hb
  | add z w hz hw => simp only [map_add, hz, hw]

end FLT.Mazur
