/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeOppositeSlope

/-!
# Equal-depth opposite branches add into E₀

The proof covers vertical lines, integral slopes and nonintegral slopes.
Only the explicit tangent conditions and normalized coefficients are used;
no component classification or label addition law is assumed.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] (A : ValuationSubring K)
  (W : WeierstrassCurve A)

/-- A nontangent integral slope through the node gives smooth reduction of the actual sum. -/
theorem smoothReduction_add_of_node_nontangent (x₁ y₁ x₂ y₂ l : A)
    (h₁ : (W.map (algebraMap A K)).toAffine.Nonsingular (x₁ : K) (y₁ : K))
    (h₂ : (W.map (algebraMap A K)).toAffine.Nonsingular (x₂ : K) (y₂ : K))
    (hxy : ¬ ((x₁ : K) = (x₂ : K) ∧ (y₁ : K) =
      (W.map (algebraMap A K)).toAffine.negY (x₂ : K) (y₂ : K)))
    (hs : (W.map (algebraMap A K)).toAffine.slope (x₁ : K) (x₂ : K)
      (y₁ : K) (y₂ : K) = (l : K))
    (h2 : W.a₂ ∈ maximalIdeal A) (h3 : W.a₃ ∈ maximalIdeal A)
    (h4 : W.a₄ ∈ maximalIdeal A) (h6 : W.a₆ ∈ maximalIdeal A)
    (hx₁ : x₁ ∈ maximalIdeal A) (hx₂ : x₂ ∈ maximalIdeal A)
    (hl : residue A l ≠ 0 ∧ residue A l ≠ -residue A W.a₁) :
    SmoothReduction A W (Affine.Point.toProjective (.some _ _ h₁ + .some _ _ h₂)) := by
  have hu := node_addX_unit_of_not_tangent W h2 hx₁ hx₂ hl
  rw [Affine.Point.add_some hxy]
  simp only [hs]
  have hx := W.toAffine.map_addX (algebraMap A K) x₁ x₂ l
  have hy := W.toAffine.map_addY (algebraMap A K) x₁ y₁ x₂ l
  change (W.map (algebraMap A K)).toAffine.addX _ _ _ = _ at hx
  change (W.map (algebraMap A K)).toAffine.addY _ _ _ _ = _ at hy
  simp only [ValuationSubring.algebraMap_apply] at hx hy
  simp only [hx, hy]
  rw [smoothReduction_affine_iff]
  have heK := (Affine.nonsingular_add h₁ h₂ hxy).1
  rw [hs, hx, hy] at heK
  have he := (W.toAffine.map_equation (IsFractionRing.injective A K)
    (W.toAffine.addX x₁ x₂ l) (W.toAffine.addY x₁ x₂ y₁ l)).mp heK
  apply (normalized_nonsingular_iff (W.map (residue A))
    (by simpa using (residue_eq_zero_iff _).mpr h3)
    (by simpa using (residue_eq_zero_iff _).mpr h4)
    (by simpa using (residue_eq_zero_iff _).mpr h6) (he.map (residue A))).mpr
  exact fun h => (residue_ne_zero_iff_isUnit _).mpr hu h.1

/-- Equal positive depths on opposite strict branches sum to the smooth-reduction subgroup. -/
theorem smoothReduction_add_of_node_opposite {π : A} (hπ : π ≠ 0)
    (hπm : π ∈ maximalIdeal A) (k : ℕ) (hk : 0 < k) (a b c d : A)
    (h₁ : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((π ^ k * a : A) : K) ((π ^ k * b : A) : K))
    (h₂ : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((π ^ k * c : A) : K) ((π ^ k * d : A) : K))
    (h1 : IsUnit W.a₁) (h2 : W.a₂ ∈ maximalIdeal A)
    (h3 : W.a₃ ∈ maximalIdeal A) (h4 : W.a₄ ∈ maximalIdeal A)
    (h6 : W.a₆ ∈ maximalIdeal A) (ha : IsUnit a)
    (hb : b ∈ maximalIdeal A) (hd : IsUnit d) (hdt : d + W.a₁ * c ∈ maximalIdeal A) :
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
    have hs : l = (u : K) := rfl
    have hu := node_equal_depth_slope_identity A W hπ k a b c d u h₁.1 h₂.1 hxy hs
    have ht := node_opposite_slope_not_tangent W ha h1 hb hd hdt hu
    have hm (e : A) : π ^ k * e ∈ maximalIdeal A :=
      (maximalIdeal A).mul_mem_right e
        (Ideal.pow_le_self (Nat.ne_of_gt hk) (Ideal.pow_mem_pow hπm k))
    exact smoothReduction_add_of_node_nontangent A W _ _ _ _ u h₁ h₂ hxy hs
      h2 h3 h4 h6 (hm a) (hm c) ht
  · rw [Affine.Point.add_some hxy]
    apply smoothReduction_of_nonintegral
    intro hi
    exact hl (slope_mem_of_addX_mem A W (π ^ k * a) (π ^ k * c) l hi.1)

end FLT.Mazur
