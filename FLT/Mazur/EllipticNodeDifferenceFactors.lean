/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeAdditionProduct
public import FLT.Mazur.EllipticNodeSecantSlope

/-!
# Primitive factors for an opposite-branch depth difference

The product formula gives a unit x-factor when the shallower slope reduces
to zero and the deeper y-factor is a unit. The line equation gives a unit
y-factor on the second branch. No unit hypothesis on the deeper x-factor
is needed, so the calculation also applies at the midpoint.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {R : Type*} [CommRing R] [IsLocalRing R] (W : WeierstrassCurve R)

/-- Reduction of the product numerator is the nonzero opposite tangent factor. -/
theorem node_difference_numerator_unit {π l d e₃ e₄ : R}
    (hπ : π ∈ maximalIdeal R) (h1 : IsUnit W.a₁) (h2 : W.a₂ ∈ maximalIdeal R)
    (hl : residue R l = 0) (hd : IsUnit d) (h4 : e₄ ∈ maximalIdeal R)
    (m : ℕ) (hm : 0 < m) (c : R) :
    IsUnit (π ^ m * c ^ 2 + (W.a₂ + l ^ 2) * c + e₄ -
      (2 * l + W.a₁) * d - e₃ * l) := by
  apply (residue_ne_zero_iff_isUnit _).mp
  simpa [show residue R π = 0 from (residue_eq_zero_iff _).mpr hπ,
    show residue R W.a₂ = 0 from (residue_eq_zero_iff _).mpr h2,
    show residue R e₄ = 0 from (residue_eq_zero_iff _).mpr h4, hl, Nat.ne_of_gt hm] using
    neg_ne_zero.mpr (mul_ne_zero ((residue_ne_zero_iff_isUnit _).mpr h1)
      ((residue_ne_zero_iff_isUnit _).mpr hd))

omit [IsLocalRing R] in
/-- The actual y-addition formula can be evaluated on the second input point. -/
theorem node_addY_from_second (x y z t l : R) (hline : (x - z) * l = y - t) :
    W.toAffine.addY x z y l = -(l + W.a₁) * W.toAffine.addX x z l + l * z - t - W.a₃ := by
  simp only [Affine.addY, Affine.negY, Affine.negAddY]
  linear_combination hline

/-- A shallower first-branch point and a deeper unit y-factor give primitive difference factors. -/
theorem exists_node_difference_factors {π a b c d l e₃ e₄ : R}
    (hπ : π ∈ maximalIdeal R) (h1 : IsUnit W.a₁) (h2 : W.a₂ ∈ maximalIdeal R)
    (ha : IsUnit a) (hd : IsUnit d) (hl : residue R l = 0)
    (he₄ : e₄ ∈ maximalIdeal R) (k j : ℕ) (hk : 0 < k)
    (h3 : W.a₃ = π ^ (k + j) * e₃)
    (hline : (π ^ k * a - π ^ (k + j) * c) * l = π ^ k * b - π ^ (k + j) * d)
    (hx : a * W.toAffine.addX (π ^ k * a) (π ^ (k + j) * c) l =
      π ^ j * (π ^ (k + j) * c ^ 2 + (W.a₂ + l ^ 2) * c + e₄ -
        (2 * l + W.a₁) * d - e₃ * l)) :
    ∃ u v : R, IsUnit u ∧ IsUnit v ∧
      W.toAffine.addX (π ^ k * a) (π ^ (k + j) * c) l = π ^ j * u ∧
      W.toAffine.addY (π ^ k * a) (π ^ (k + j) * c) (π ^ k * b) l = π ^ j * v := by
  let r := π ^ (k + j) * c ^ 2 + (W.a₂ + l ^ 2) * c + e₄ - (2 * l + W.a₁) * d - e₃ * l
  have hr : IsUnit r := node_difference_numerator_unit W hπ h1 h2 hl hd he₄ (k + j) (by omega) c
  obtain ⟨a', ha'⟩ := ha
  let u : R := r * ↑a'⁻¹
  let v : R := -(l + W.a₁) * u + π ^ k * (l * c - d - e₃)
  have hu : IsUnit u := hr.mul a'⁻¹.isUnit
  have hx' : W.toAffine.addX (π ^ k * a) (π ^ (k + j) * c) l = π ^ j * u := by
    calc
      _ = ↑a'⁻¹ * (a * W.toAffine.addX (π ^ k * a) (π ^ (k + j) * c) l) := by
        rw [← ha']
        simp
      _ = π ^ j * u := by rw [hx]; dsimp [u, r]; ring
  refine ⟨u, v, hu, ?_, hx', ?_⟩
  · apply (residue_ne_zero_iff_isUnit _).mp
    simpa [v, hl, show residue R π = 0 from (residue_eq_zero_iff _).mpr hπ,
      Nat.ne_of_gt hk] using neg_ne_zero.mpr
        (mul_ne_zero ((residue_ne_zero_iff_isUnit _).mpr h1)
          ((residue_ne_zero_iff_isUnit _).mpr hu))
  · rw [node_addY_from_second W _ _ _ _ _ hline, hx', h3, pow_add]
    dsimp [v]
    ring

end FLT.Mazur
