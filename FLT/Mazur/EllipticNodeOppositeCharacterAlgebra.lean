/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeOppositeSlope

/-!
# Residue algebra for opposite-branch sums

Integral slopes determine the multiplicative parameter of the smooth output.
A nonintegral slope forces the divided horizontal residues to coincide, which
is the same character identity at the point at infinity.
-/

@[expose] public section
namespace FLT.Mazur
open IsLocalRing WeierstrassCurve

/-- The addition formulas at the node retain the line slope in their residue. -/
theorem node_add_coordinate_residues {R : Type*} [CommRing R] [IsLocalRing R]
    (W : WeierstrassCurve R) {x₁ y₁ x₂ l : R}
    (h2 : W.a₂ ∈ maximalIdeal R) (h3 : W.a₃ ∈ maximalIdeal R)
    (hx₁ : x₁ ∈ maximalIdeal R) (hy₁ : y₁ ∈ maximalIdeal R) (hx₂ : x₂ ∈ maximalIdeal R) :
    residue R (W.toAffine.addX x₁ x₂ l) = residue R l * (residue R l + residue R W.a₁) ∧
      residue R (W.toAffine.addY x₁ x₂ y₁ l) =
        -(residue R l + residue R W.a₁) * residue R (W.toAffine.addX x₁ x₂ l) := by
  have h20 := (residue_eq_zero_iff _).mpr h2
  have h30 := (residue_eq_zero_iff _).mpr h3
  have hx10 := (residue_eq_zero_iff _).mpr hx₁
  have hy10 := (residue_eq_zero_iff _).mpr hy₁
  have hx20 := (residue_eq_zero_iff _).mpr hx₂
  constructor
  · simp only [Affine.addX, map_sub, map_add, map_pow, map_mul, h20, hx10, hx20]
    ring
  · simp only [Affine.addY, Affine.negY, Affine.negAddY, map_sub, map_add, map_neg, map_mul,
      hx10, hy10, h30]
    ring

/-- The character of the reflected line slope, expressed in original branch residues. -/
theorem node_opposite_slope_character {R : Type*} [CommRing R] [IsLocalRing R]
    (W : WeierstrassCurve R) {a b c d l : R} (ha : IsUnit a) (h1 : IsUnit W.a₁)
    (hb : b ∈ maximalIdeal R) (hd : IsUnit d) (hdt : d + W.a₁ * c ∈ maximalIdeal R)
    (hl : (a - c) * l = b - d) :
    residue R d * ((residue R l + residue R W.a₁) / residue R l) =
      -residue R (b + W.a₁ * a) := by
  have hn := (node_opposite_slope_not_tangent W ha h1 hb hd hdt hl).1
  have he := congrArg (residue R) hl
  have ht := (residue_eq_zero_iff _).mpr hdt
  have hb0 := (residue_eq_zero_iff _).mpr hb
  simp only [map_mul, map_sub, hb0, zero_sub] at he
  simp only [map_add, map_mul] at ht
  rw [map_add, map_mul, hb0, zero_add]
  apply (mul_right_cancel₀ hn)
  field_simp
  linear_combination residue R W.a₁ * he + residue R l * ht

/-- A nonintegral line slope cannot have a unit divided horizontal difference. -/
theorem node_nonintegral_line_residue {K : Type*} [Field K]
    (A : ValuationSubring K) {a b c d : A} {l : K}
    (hl : ((a : K) - c) * l = (b : K) - d) (hn : l ∉ A) :
    residue A a = residue A c := by
  by_contra hne
  have hu : IsUnit (a - c) := (residue_ne_zero_iff_isUnit _).mp (by
    simpa only [map_sub, sub_ne_zero] using hne)
  let q : A := (↑hu.unit⁻¹ : A) * (b - d)
  have he : (q : K) = l := by
    apply mul_left_cancel₀ (show ((a - c : A) : K) ≠ 0 from
      (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hu.ne_zero)
    calc
      ((a - c : A) : K) * (q : K) = ((b - d : A) : K) := by
        change algebraMap A K ((a - c) * q) = algebraMap A K (b - d)
        congr 1
        dsimp [q]
        have hi : (a - c) * (↑hu.unit⁻¹ : A) = 1 := hu.mul_val_inv
        rw [← mul_assoc, hi, one_mul]
      _ = ((a - c : A) : K) * l := hl.symm
  exact hn (he ▸ q.property)

/-- Equal divided horizontal residues give the opposite character law at infinity. -/
theorem node_opposite_equal_horizontal_character {R : Type*} [CommRing R] [IsLocalRing R]
    (W : WeierstrassCurve R) {a b c d : R}
    (hb : b ∈ maximalIdeal R) (hdt : d + W.a₁ * c ∈ maximalIdeal R)
    (he : residue R a = residue R c) :
    residue R d = -residue R (b + W.a₁ * a) := by
  have ht := (residue_eq_zero_iff _).mpr hdt
  rw [map_add, map_mul] at ht
  rw [map_add, map_mul, (residue_eq_zero_iff _).mpr hb, zero_add, he]
  linear_combination ht

end FLT.Mazur
