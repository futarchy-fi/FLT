/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSplitDepthResidueCharacter
public import FLT.Mazur.EllipticNodeOppositeCharacterAlgebra

/-!
# The smooth character of an integral opposite-branch sum

For an actual integral slope joining equal-depth opposite branches, the smooth
output character is the negative quotient of the original input characters.
The statement computes the actual projective reduction relation.
-/

@[expose] public section
namespace FLT.Mazur
open IsLocalRing WeierstrassCurve
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  [DecidableEq (ResidueField A)]

/-- The character of an integral addition output at the node comes from its line slope. -/
theorem splitDepthResidueCharacter_node_add
    (x₁ y₁ x₂ l : A) (hx₁ : x₁ ∈ maximalIdeal A)
    (hy₁ : y₁ ∈ maximalIdeal A) (hx₂ : x₂ ∈ maximalIdeal A)
    (hl : residue A l ≠ 0 ∧ residue A l ≠ -residue A W.a₁)
    (hr : (W.map (residue A)).toAffine.Nonsingular
      (residue A (W.toAffine.addX x₁ x₂ l)) (residue A (W.toAffine.addY x₁ x₂ y₁ l))) :
    (Additive.toMul (splitDepthResidueCharacter D (.some _ _ hr))).val =
      (residue A l + residue A W.a₁) / residue A l := by
  have h3 := Ideal.pow_le_self (show n + 1 ≠ 0 by omega) D.a₃_mem
  obtain ⟨hx, hy⟩ := node_add_coordinate_residues W D.a₂_mem h3 hx₁ hy₁ hx₂
  have hxu := node_addX_unit_of_not_tangent W D.a₂_mem hx₁ hx₂ hl
  have hxn := (residue_ne_zero_iff_isUnit _).mpr hxu
  rw [splitDepthResidueCharacter_some, hy, mul_div_cancel_right₀ _ hxn]
  have he : -(residue A l + residue A W.a₁) + residue A W.a₁ = -residue A l := by ring
  rw [he, neg_div_neg_eq]

variable [DecidableEq K]

/-- An arbitrary smooth reduced point of the actual sum has the opposite-branch character. -/
theorem node_integral_opposite_reduction_character (k : ℕ) (hk : 0 < k)
    (a b c d l : A)
    (h₁ : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((π ^ k * a : A) : K) ((π ^ k * b : A) : K))
    (h₂ : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((π ^ k * c : A) : K) ((π ^ k * d : A) : K))
    (ha : IsUnit a) (hb : b ∈ maximalIdeal A) (hd : IsUnit d)
    (hdt : d + W.a₁ * c ∈ maximalIdeal A)
    (hxy : ¬ (((π ^ k * a : A) : K) = ((π ^ k * c : A) : K) ∧
      ((π ^ k * b : A) : K) = (W.map (algebraMap A K)).toAffine.negY
        ((π ^ k * c : A) : K) ((π ^ k * d : A) : K)))
    (hl : (W.map (algebraMap A K)).toAffine.slope
      ((π ^ k * a : A) : K) ((π ^ k * c : A) : K)
      ((π ^ k * b : A) : K) ((π ^ k * d : A) : K) = (l : K))
    (q : (W.map (residue A)).toAffine.Point)
    (hq : ReducesTo A W (.some _ _ h₁ + .some _ _ h₂) q) :
    residue A d * (Additive.toMul (splitDepthResidueCharacter D q)).val =
      -residue A (b + W.a₁ * a) := by
  have hline := node_equal_depth_slope_identity A W D.uniformizer_ne_zero k a b c d l
    h₁.1 h₂.1 hxy hl
  have ht := node_opposite_slope_not_tangent W ha D.a₁_unit hb hd hdt hline
  have hπm : π ∈ maximalIdeal A := D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  have hm (e : A) : π ^ k * e ∈ maximalIdeal A :=
    (maximalIdeal A).mul_mem_right e
      (Ideal.pow_le_self (Nat.ne_of_gt hk) (Ideal.pow_mem_pow hπm k))
  rw [Affine.Point.add_some hxy] at hq
  simp only [hl] at hq
  have hx := W.toAffine.map_addX (algebraMap A K) (π ^ k * a) (π ^ k * c) l
  have hy := W.toAffine.map_addY (algebraMap A K) (π ^ k * a) (π ^ k * b) (π ^ k * c) l
  change (W.map (algebraMap A K)).toAffine.addX _ _ _ = _ at hx
  change (W.map (algebraMap A K)).toAffine.addY _ _ _ _ = _ at hy
  simp only [ValuationSubring.algebraMap_apply] at hx hy
  simp only [hx, hy] at hq
  have hr := (smoothReduction_affine_iff A W _ _ _).mp
    ((exists_reducesTo_iff A W _).mp ⟨q, hq⟩)
  have he := hq.unique A W (reducesTo_integral A W _ _ _ hr)
  rw [he, splitDepthResidueCharacter_node_add D _ _ _ l (hm a) (hm b) (hm c) ht hr]
  exact node_opposite_slope_character W ha D.a₁_unit hb hd hdt hline

end FLT.Mazur
