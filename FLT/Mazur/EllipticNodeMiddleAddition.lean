/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeEqualDepthSlope
public import FLT.Mazur.EllipticNodeOppositeAddition
public import FLT.Mazur.EllipticNodeComponentLabel

/-!
# Addition of two middle-depth points

Both tangent factors at the middle depth are units. The second slope identity
then excludes either nodal tangent for an integral slope; a nonintegral slope
reduces to infinity. Consequently the middle component has order at most two.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

/-- Unit tangent factors rule out both nodal tangents in the second slope identity. -/
theorem node_middle_slope_not_tangent {R : Type*} [CommRing R] [IsLocalRing R]
    (W : WeierstrassCurve R) {b c d l : R} (h1 : IsUnit W.a₁)
    (hb : IsUnit b) (hd : IsUnit (d + W.a₁ * c))
    (hl : (residue R b + residue R d + residue R W.a₁ * residue R c) * residue R l =
      -(residue R W.a₁ * residue R b)) :
    residue R l ≠ 0 ∧ residue R l ≠ -residue R W.a₁ := by
  have h10 := (residue_ne_zero_iff_isUnit _).mpr h1
  have hb0 := (residue_ne_zero_iff_isUnit _).mpr hb
  have hd0 := (residue_ne_zero_iff_isUnit _).mpr hd
  simp only [map_add, map_mul] at hd0
  constructor
  · intro hz
    rw [hz, mul_zero] at hl
    exact mul_ne_zero h10 hb0 (neg_eq_zero.mp hl.symm)
  · intro hz
    rw [hz] at hl
    apply mul_ne_zero h10 hd0
    linear_combination -hl

variable {K : Type*} [Field K] [DecidableEq K] (A : ValuationSubring K)
  (W : WeierstrassCurve A)

/-- Actual equal-depth addition with unit opposite tangent factors has smooth reduction. -/
theorem smoothReduction_add_of_node_middle {π : A} (hπ : π ≠ 0)
    (hgen : maximalIdeal A = Ideal.span {π}) (k : ℕ) (hk : 0 < k) (a b c d : A)
    (h₁ : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((π ^ k * a : A) : K) ((π ^ k * b : A) : K))
    (h₂ : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((π ^ k * c : A) : K) ((π ^ k * d : A) : K))
    (h1 : IsUnit W.a₁) (h2 : W.a₂ ∈ maximalIdeal A)
    (h3 : W.a₃ ∈ maximalIdeal A ^ (k + 1)) (h4 : W.a₄ ∈ maximalIdeal A ^ (k + 1))
    (h6 : W.a₆ ∈ maximalIdeal A) (hb : IsUnit b) (hd : IsUnit (d + W.a₁ * c)) :
    SmoothReduction A W (Affine.Point.toProjective (.some _ _ h₁ + .some _ _ h₂)) := by
  by_cases hxy : ((π ^ k * a : A) : K) = ((π ^ k * c : A) : K) ∧
      ((π ^ k * b : A) : K) = (W.map (algebraMap A K)).toAffine.negY
        ((π ^ k * c : A) : K) ((π ^ k * d : A) : K)
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
    exact smoothReduction_zero A W
  let l := (W.map (algebraMap A K)).toAffine.slope
    ((π ^ k * a : A) : K) ((π ^ k * c : A) : K)
    ((π ^ k * b : A) : K) ((π ^ k * d : A) : K)
  by_cases hl : l ∈ A
  · let u : A := ⟨l, hl⟩
    obtain ⟨e₃, he₃, h3e⟩ := exists_node_deep_factor hgen k h3
    obtain ⟨e₄, he₄, h4e⟩ := exists_node_deep_factor hgen k h4
    have hπm : π ∈ maximalIdeal A := hgen ▸ Ideal.mem_span_singleton_self π
    have hr := node_equal_depth_second_residue A W hπ hπm k hk a b c d u e₃ e₄
      h2 he₃ he₄ h3e h4e h₁.1 h₂.1 hxy rfl
    have ht := node_middle_slope_not_tangent W h1 hb hd hr
    have hm (e : A) : π ^ k * e ∈ maximalIdeal A :=
      (maximalIdeal A).mul_mem_right e
        (Ideal.pow_le_self (Nat.ne_of_gt hk) (Ideal.pow_mem_pow hπm k))
    exact smoothReduction_add_of_node_nontangent A W _ _ _ _ u h₁ h₂ hxy rfl
      h2 (Ideal.pow_le_self (by omega) h3) (Ideal.pow_le_self (by omega) h4)
      h6 (hm a) (hm c) ht
  · rw [Affine.Point.add_some hxy]
    apply smoothReduction_of_nonintegral
    intro hi
    exact hl (slope_mem_of_addX_mem A W (π ^ k * a) (π ^ k * c) l hi.1)

end FLT.Mazur
