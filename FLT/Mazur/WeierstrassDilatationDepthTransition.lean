/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationRefinement

/-!
# Actual transitions between divided charts at arbitrary depths

Two factorizations of the same original coefficients force the transition
coefficients by cancellation. They therefore construct a map between the
actual depth charts, without assuming compatibility of chosen quotients.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R]
  (π : R) (k l : ℕ) (hπ : π ≠ 0) (hkl : k ≤ l)

include hπ hkl in
/-- Dividing the same coefficient at two depths forces the intervening scale factor. -/
theorem depth_coefficient_factor {z b c : R} (hb : z = π ^ k * b) (hc : z = π ^ l * c) :
    b = π ^ (l - k) * c := by
  apply mul_left_cancel₀ (pow_ne_zero k hπ)
  rw [← hb, hc, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hkl]

include hπ hkl in
/-- The constant coefficient has the square of the same intervening scale factor. -/
theorem depth_constant_factor {z b c : R}
    (hb : z = (π ^ k) ^ 2 * b) (hc : z = (π ^ l) ^ 2 * c) :
    b = (π ^ (l - k)) ^ 2 * c := by
  apply mul_left_cancel₀ (pow_ne_zero 2 (pow_ne_zero k hπ))
  rw [← hb, hc, ← mul_assoc, ← mul_pow, ← pow_add, Nat.add_sub_of_le hkl]

variable (W : WeierstrassCurve R) (b3 b4 b6 c3 c4 c6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6)
  (H3 : W.a₃ = π ^ l * c3) (H4 : W.a₄ = π ^ l * c4)
  (H6 : W.a₆ = (π ^ l) ^ 2 * c6)
local notation "B" => Coordinate W (π ^ k) b3 b4 b6
local notation "C" => Coordinate W (π ^ l) c3 c4 c6
local notation "X" => x W (π ^ l) c3 c4 c6
local notation "Y" => y W (π ^ l) c3 c4 c6
local notation "S" => algebraMap R C (π ^ (l - k))

include hπ hkl h3 h4 h6 H3 H4 H6 in
/-- The actual deeper universal coordinates solve the preceding divided equation. -/
theorem depthTransition_equation :
    (S * Y) ^ 2 + (algebraMap R C W.a₁ * (S * X) + algebraMap R C b3) * (S * Y) =
      algebraMap R C (π ^ k) * (S * X) ^ 3 + algebraMap R C W.a₂ * (S * X) ^ 2 +
        algebraMap R C b4 * (S * X) + algebraMap R C b6 := by
  have h := equation W (π ^ l) c3 c4 c6
  have hs : algebraMap R C (π ^ l) = algebraMap R C (π ^ k) * S := by
    rw [← map_mul, ← pow_add, Nat.add_sub_of_le hkl]
  rw [hs] at h
  rw [depth_coefficient_factor π k l hπ hkl h3 H3,
    depth_coefficient_factor π k l hπ hkl h4 H4,
    depth_constant_factor π k l hπ hkl h6 H6]
  simp only [map_mul, map_pow]
  simp only [map_pow] at h
  linear_combination ((algebraMap R C π) ^ (l - k)) ^ 2 * h

/-- The actual coordinate map between any two compatible original depth charts. -/
def depthTransition : B →ₐ[R] C :=
  evaluation W (π ^ k) b3 b4 b6 (S * X) (S * Y)
    (depthTransition_equation π k l hπ hkl W b3 b4 b6 c3 c4 c6 h3 h4 h6 H3 H4 H6)

/-- The old first coordinate is the intervening power times the new coordinate. -/
@[simp] theorem depthTransition_x :
    depthTransition π k l hπ hkl W b3 b4 b6 c3 c4 c6 h3 h4 h6 H3 H4 H6
      (x W (π ^ k) b3 b4 b6) = S * X := evaluation_x _ _ _ _ _ _ _ _
/-- The old second coordinate uses exactly the same intervening power. -/
@[simp] theorem depthTransition_y :
    depthTransition π k l hπ hkl W b3 b4 b6 c3 c4 c6 h3 h4 h6 H3 H4 H6
      (y W (π ^ k) b3 b4 b6) = S * Y := evaluation_y _ _ _ _ _ _ _ _

/-- Every depth transition retains the original affine cubic coordinate map. -/
theorem depthTransition_fromOriginal :
    (depthTransition π k l hπ hkl W b3 b4 b6 c3 c4 c6 h3 h4 h6 H3 H4 H6).comp
        (fromOriginal W (π ^ k) b3 b4 b6 h3 h4 h6) =
      fromOriginal W (π ^ l) c3 c4 c6 H3 H4 H6 := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i <;>
    simp [WeierstrassIntegralChart.coord_self, ← mul_assoc,
      ← pow_add, Nat.add_sub_of_le hkl]

end FLT.Mazur.WeierstrassDilatation
