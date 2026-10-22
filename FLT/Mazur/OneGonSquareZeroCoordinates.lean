/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingEquation
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Integral coordinates normalizing an infinitesimal split node

The four correction coordinates solve the linear coefficient equations at
`y² - xy = x³`. Their formulas use integers only, including at 2 and 3.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.OneGonSquareZero
variable {R : Type*} [CommRing R]

/-- Products of two elements of a square-zero ideal vanish. -/
theorem mul_eq_zero (I : Ideal R) (hI : I ^ 2 = ⊥)
    {a b : R} (ha : a ∈ I) (hb : b ∈ I) : a * b = 0 := by
  have h := Ideal.mul_mem_mul ha hb
  rw [← pow_two, hI, Ideal.mem_bot] at h
  exact h

/-- The horizontal correction of the singular point. -/
def shiftX (W : WeierstrassCurve R) : R := W.a₃ - 2 * W.a₄

/-- The vertical correction of the singular point. -/
def shiftY (W : WeierstrassCurve R) : R := -W.a₄

/-- The shear correcting the tangent direction. -/
def shear (W : WeierstrassCurve R) : R := -W.a₂ - 3 * shiftX W

/-- The infinitesimal correction of the scaling unit. -/
def scaleError (W : WeierstrassCurve R) : R := -(W.a₁ + 1) - 2 * shear W

variable (W : WeierstrassCurve R) (I : Ideal R)

/-- The horizontal correction lies in the original infinitesimal ideal. -/
theorem shiftX_mem (h₃ : W.a₃ ∈ I) (h₄ : W.a₄ ∈ I) : shiftX W ∈ I :=
  I.sub_mem h₃ (I.mul_mem_left 2 h₄)

/-- The vertical correction lies in the original infinitesimal ideal. -/
theorem shiftY_mem (h₄ : W.a₄ ∈ I) : shiftY W ∈ I := I.neg_mem h₄

/-- The tangent shear lies in the original infinitesimal ideal. -/
theorem shear_mem (h₂ : W.a₂ ∈ I) (h₃ : W.a₃ ∈ I) (h₄ : W.a₄ ∈ I) :
    shear W ∈ I := I.sub_mem (I.neg_mem h₂) (I.mul_mem_left 3 (shiftX_mem W I h₃ h₄))

/-- The scaling error lies in the original infinitesimal ideal. -/
theorem scaleError_mem (h₁ : W.a₁ + 1 ∈ I) (h₂ : W.a₂ ∈ I)
    (h₃ : W.a₃ ∈ I) (h₄ : W.a₄ ∈ I) : scaleError W ∈ I :=
  I.sub_mem (I.neg_mem h₁) (I.mul_mem_left 2 (shear_mem W I h₂ h₃ h₄))

/-- The scaling correction is a unit with an explicit integral inverse. -/
def scaleUnit (h : scaleError W * scaleError W = 0) : Rˣ where
  val := 1 + scaleError W
  inv := 1 - scaleError W
  val_inv := by linear_combination -h
  inv_val := by linear_combination -h

/-- The actual admissible coordinate change, with no characteristic restriction. -/
def change (h : scaleError W * scaleError W = 0) : VariableChange R :=
  ⟨scaleUnit W h, shiftX W, shear W, shiftY W⟩

/-- A square-zero thickening supplies the required scaling identity. -/
theorem scaleError_square (hI : I ^ 2 = ⊥) (h₁ : W.a₁ + 1 ∈ I)
    (h₂ : W.a₂ ∈ I) (h₃ : W.a₃ ∈ I) (h₄ : W.a₄ ∈ I) :
    scaleError W * scaleError W = 0 :=
  mul_eq_zero I hI (scaleError_mem W I h₁ h₂ h₃ h₄)
    (scaleError_mem W I h₁ h₂ h₃ h₄)

end FLT.Mazur.OneGonSquareZero
