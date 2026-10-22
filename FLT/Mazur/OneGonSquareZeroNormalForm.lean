/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSquareZeroCoordinates

/-!
# Normal form for arbitrary square-zero deformations of the nodal equation

Every Weierstrass equation reducing to the split node over a square-zero
ideal admits an explicit admissible change to the arithmetic one-gon family.
The statement concerns the original equation, not just its discriminant.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.OneGonSquareZero
variable {R : Type*} [CommRing R]

/-- Scaling acts trivially on first-order coefficients. -/
theorem inverse_scale_pow_mul (v x : R) (h : v * x = 0) (n : ℕ) :
    (1 - v) ^ n * x = x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_assoc, sub_mul, one_mul, h, sub_zero, ih]

/-- The four integral corrections normalize the original square-zero deformation. -/
theorem change_normalForm (W : WeierstrassCurve R) (I : Ideal R) (hI : I ^ 2 = ⊥)
    (h₁ : W.a₁ + 1 ∈ I) (h₂ : W.a₂ ∈ I) (h₃ : W.a₃ ∈ I)
    (h₄ : W.a₄ ∈ I) :
    change W (scaleError_square W I hI h₁ h₂ h₃ h₄) • W =
      OneGonSmoothing.equation
        (change W (scaleError_square W I hI h₁ h₂ h₃ h₄) • W).a₆ := by
  let h := scaleError_square W I hI h₁ h₂ h₃ h₄
  have hr := shiftX_mem W I h₃ h₄
  have ht := shiftY_mem W I h₄
  have hs := shear_mem W I h₂ h₃ h₄
  have hz : ∀ {a b : R}, a ∈ I → b ∈ I → a * b = 0 := mul_eq_zero I hI
  have e₁ : W.a₁ + 2 * shear W = -(1 + scaleError W) := by
    dsimp [scaleError]
    ring
  have e₂ : W.a₂ - shear W * W.a₁ + 3 * shiftX W - shear W ^ 2 = 0 := by
    have e : W.a₂ + shear W + 3 * shiftX W = 0 := by dsimp [shear]; ring
    linear_combination e - hz hs h₁ - hz hs hs
  have e₃ : W.a₃ + shiftX W * W.a₁ + 2 * shiftY W = 0 := by
    have e : W.a₃ - shiftX W + 2 * shiftY W = 0 := by dsimp [shiftX, shiftY]; ring
    linear_combination e + hz hr h₁
  have e₄ : W.a₄ - shear W * W.a₃ + 2 * shiftX W * W.a₂ -
      (shiftY W + shiftX W * shear W) * W.a₁ + 3 * shiftX W ^ 2 -
      2 * shear W * shiftY W = 0 := by
    have e : W.a₄ + shiftY W = 0 := by dsimp [shiftY]; ring
    linear_combination e - hz hs h₃ + 2 * hz hr h₂ - hz ht h₁ -
      W.a₁ * hz hr hs + 3 * hz hr hr - 2 * hz hs ht
  apply WeierstrassCurve.ext
  · rw [variableChange_a₁]
    change (↑((scaleUnit W h)⁻¹) : R) * (W.a₁ + 2 * shear W) = -1
    rw [e₁]
    change (↑((scaleUnit W h)⁻¹) : R) * -(scaleUnit W h : R) = -1
    simp
  · rw [variableChange_a₂]
    dsimp only [change]
    change (1 - scaleError W) ^ 2 * _ = 0
    rw [e₂, mul_zero]
  · rw [variableChange_a₃]
    dsimp only [change]
    change (1 - scaleError W) ^ 3 * _ = 0
    rw [e₃, mul_zero]
  · rw [variableChange_a₄]
    dsimp only [change]
    change (1 - scaleError W) ^ 4 * _ = 0
    rw [e₄, mul_zero]
  · rfl

/-- The remaining coefficient is unchanged when it also lies in the square-zero ideal. -/
theorem change_a₆ (W : WeierstrassCurve R) (I : Ideal R) (hI : I ^ 2 = ⊥)
    (h₁ : W.a₁ + 1 ∈ I) (h₂ : W.a₂ ∈ I) (h₃ : W.a₃ ∈ I)
    (h₄ : W.a₄ ∈ I) (h₆ : W.a₆ ∈ I) :
    (change W (scaleError_square W I hI h₁ h₂ h₃ h₄) • W).a₆ = W.a₆ := by
  have hr := shiftX_mem W I h₃ h₄
  have ht := shiftY_mem W I h₄
  have hv := scaleError_mem W I h₁ h₂ h₃ h₄
  have hz : ∀ {a b : R}, a ∈ I → b ∈ I → a * b = 0 := mul_eq_zero I hI
  have e₆ : W.a₆ + shiftX W * W.a₄ + shiftX W ^ 2 * W.a₂ + shiftX W ^ 3 -
      shiftY W * W.a₃ - shiftY W ^ 2 - shiftX W * shiftY W * W.a₁ = W.a₆ := by
    linear_combination hz hr h₄ + (W.a₂ + shiftX W) * hz hr hr -
      hz ht h₃ - hz ht ht - W.a₁ * hz hr ht
  rw [variableChange_a₆]
  dsimp only [change]
  change (1 - scaleError W) ^ 6 * _ = W.a₆
  rw [e₆]
  exact inverse_scale_pow_mul _ _ (hz hv h₆) 6

/-- The original first-order deformation is the family at its own constant coefficient. -/
theorem change_equation (W : WeierstrassCurve R) (I : Ideal R) (hI : I ^ 2 = ⊥)
    (h₁ : W.a₁ + 1 ∈ I) (h₂ : W.a₂ ∈ I) (h₃ : W.a₃ ∈ I)
    (h₄ : W.a₄ ∈ I) (h₆ : W.a₆ ∈ I) :
    change W (scaleError_square W I hI h₁ h₂ h₃ h₄) • W =
      OneGonSmoothing.equation W.a₆ := by
  rw [change_normalForm W I hI h₁ h₂ h₃ h₄, change_a₆ W I hI h₁ h₂ h₃ h₄ h₆]

/-- Every such original equation has an actual admissible one-gon presentation. -/
theorem exists_change (W : WeierstrassCurve R) (I : Ideal R) (hI : I ^ 2 = ⊥)
    (h₁ : W.a₁ + 1 ∈ I) (h₂ : W.a₂ ∈ I) (h₃ : W.a₃ ∈ I)
    (h₄ : W.a₄ ∈ I) (h₆ : W.a₆ ∈ I) :
    ∃ C : VariableChange R, C • W = OneGonSmoothing.equation W.a₆ :=
  ⟨change W (scaleError_square W I hI h₁ h₂ h₃ h₄),
    change_equation W I hI h₁ h₂ h₃ h₄ h₆⟩

end FLT.Mazur.OneGonSquareZero
