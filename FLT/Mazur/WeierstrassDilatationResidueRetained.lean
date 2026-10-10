/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationResidueFiber
public import FLT.Mazur.WeierstrassDilatationParameterCongruence

/-!
# Retained divided coordinates in the actual residue fiber

Normalize only the vanishing coefficients, keeping the original horizontal
and vertical generators and the actual residue of the divided constant.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (S : Type*) [CommRing S] [Algebra R S]

/-- The original horizontal coordinate included into the actual tensor algebra. -/
def tensorX : ScalarExtension W s b3 b4 b6 S :=
  Algebra.TensorProduct.includeRight (x W s b3 b4 b6)

/-- The original vertical coordinate included into the actual tensor algebra. -/
def tensorY : ScalarExtension W s b3 b4 b6 S :=
  Algebra.TensorProduct.includeRight (y W s b3 b4 b6)

/-- Coefficient extension retains the original tensor horizontal generator. -/
@[simp] theorem baseChangeEquiv_tensorX :
    baseChangeEquiv W s b3 b4 b6 S (tensorX W s b3 b4 b6 S) =
      x (W.map (algebraMap R S)) (algebraMap R S s)
        (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6) := by
  change baseChangeForward W s b3 b4 b6 S (tensorX W s b3 b4 b6 S) = _
  rw [tensorX, Algebra.TensorProduct.includeRight_apply,
    baseChangeForward_tmul, one_smul, coefficientMap_x]

/-- Coefficient extension retains the original tensor vertical generator. -/
@[simp] theorem baseChangeEquiv_tensorY :
    baseChangeEquiv W s b3 b4 b6 S (tensorY W s b3 b4 b6 S) =
      y (W.map (algebraMap R S)) (algebraMap R S s)
        (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6) := by
  change baseChangeForward W s b3 b4 b6 S (tensorY W s b3 b4 b6 S) = _
  rw [tensorY, Algebra.TensorProduct.includeRight_apply,
    baseChangeForward_tmul, one_smul, coefficientMap_y]

variable [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ n)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
local notation "K" => ResidueField R
local notation "W₀" => W.map (residue R)

/-- Retain the divided coordinates while normalizing the residue equation. -/
def residueRetainedCoordinateEquiv : ExtendedCoordinate W (π ^ k) b3 b4 b6 K ≃ₐ[K]
    Coordinate W₀ 0 0 0 (residue R b6) := by
  obtain ⟨hb3, hb4⟩ := divided_linear_mem D k hk b3 b4 h3 h4
  exact parameterEquiv W₀ _ _ _ _ _ _ _ _
    (residue_scale_eq_zero D k hk0) ((residue_eq_zero_iff _).mpr hb3)
    ((residue_eq_zero_iff _).mpr hb4) rfl

/-- The retained normal form is an equivalence of the actual tensor residue fiber. -/
def residueRetainedTensorEquiv : ScalarExtension W (π ^ k) b3 b4 b6 K ≃ₐ[K]
    Coordinate W₀ 0 0 0 (residue R b6) :=
  (baseChangeEquiv W (π ^ k) b3 b4 b6 K).trans
    (residueRetainedCoordinateEquiv b3 b4 b6 D k hk0 hk h3 h4)

/-- The horizontal tensor generator remains the original normalized x. -/
@[simp] theorem residueRetainedTensorEquiv_x :
    residueRetainedTensorEquiv b3 b4 b6 D k hk0 hk h3 h4
      (tensorX W (π ^ k) b3 b4 b6 K) = x W₀ 0 0 0 (residue R b6) := by
  simp only [residueRetainedTensorEquiv, AlgEquiv.trans_apply, baseChangeEquiv_tensorX]
  exact parameterEquiv_x _ _ _ _ _ _ _ _ _ _ _ _ rfl

/-- The vertical tensor generator remains the original normalized y. -/
@[simp] theorem residueRetainedTensorEquiv_y :
    residueRetainedTensorEquiv b3 b4 b6 D k hk0 hk h3 h4
      (tensorY W (π ^ k) b3 b4 b6 K) = y W₀ 0 0 0 (residue R b6) := by
  simp only [residueRetainedTensorEquiv, AlgEquiv.trans_apply, baseChangeEquiv_tensorY]
  exact parameterEquiv_y _ _ _ _ _ _ _ _ _ _ _ _ rfl

end FLT.Mazur.WeierstrassDilatation
