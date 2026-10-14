/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeDifferenceFactors

/-!
# Residues of the primitive depth-difference factors

Cancelling the uniformizer in the product and line identities retains the
leading coefficients of the actual sum. In particular the output vertical
character is determined by the input horizontal and vertical characters.
-/

@[expose] public section
namespace FLT.Mazur
open IsLocalRing WeierstrassCurve
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  (W : WeierstrassCurve R)

/-- The depth-difference addition factors retain both leading coefficients. -/
theorem node_difference_factor_residues {π a b c d l e₃ e₄ u v : R}
    (hπ0 : π ≠ 0) (hπ : π ∈ maximalIdeal R) (h2 : W.a₂ ∈ maximalIdeal R)
    (hl : residue R l = 0) (he₄ : e₄ ∈ maximalIdeal R)
    (k j : ℕ) (hk : 0 < k) (h3 : W.a₃ = π ^ (k + j) * e₃)
    (hline : (π ^ k * a - π ^ (k + j) * c) * l = π ^ k * b - π ^ (k + j) * d)
    (hprod : a * W.toAffine.addX (π ^ k * a) (π ^ (k + j) * c) l =
      π ^ j * (π ^ (k + j) * c ^ 2 + (W.a₂ + l ^ 2) * c + e₄ -
        (2 * l + W.a₁) * d - e₃ * l))
    (hx : W.toAffine.addX (π ^ k * a) (π ^ (k + j) * c) l = π ^ j * u)
    (hy : W.toAffine.addY (π ^ k * a) (π ^ (k + j) * c) (π ^ k * b) l = π ^ j * v) :
    residue R a * residue R u = -residue R W.a₁ * residue R d ∧
      residue R v = -residue R W.a₁ * residue R u := by
  have hπr := (residue_eq_zero_iff _).mpr hπ
  have h2r := (residue_eq_zero_iff _).mpr h2
  have h4r := (residue_eq_zero_iff _).mpr he₄
  have hxu : a * u = π ^ (k + j) * c ^ 2 + (W.a₂ + l ^ 2) * c + e₄ -
      (2 * l + W.a₁) * d - e₃ * l := by
    apply mul_left_cancel₀ (pow_ne_zero j hπ0)
    rw [hx] at hprod
    linear_combination hprod
  have hyv : v = -(l + W.a₁) * u + π ^ k * (l * c - d - e₃) := by
    apply mul_left_cancel₀ (pow_ne_zero j hπ0)
    rw [node_addY_from_second W _ _ _ _ _ hline, hx, h3, pow_add] at hy
    linear_combination -hy
  constructor
  · have h := congrArg (residue R) hxu
    simpa [hπr, h2r, h4r, hl, zero_pow (show k + j ≠ 0 by omega)] using h
  · have h := congrArg (residue R) hyv
    simpa [hπr, hl, Nat.ne_of_gt hk] using h

omit [IsDomain R] [IsLocalRing R] in
/-- The output vertical Laurent parameter satisfies a cleared quotient formula. -/
theorem node_difference_vertical_character {a d u v α : R}
    (hx : a * u = -α * d) (hy : v = -α * u) : a * v = α ^ 2 * d := by
  rw [hy]
  linear_combination -α * hx

end FLT.Mazur
