/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeIntegralOppositeCharacter

/-!
# Opposite-branch characters through all slope charts

Equal-depth opposite inputs satisfy the character law in the actual smooth
reduction. Vertical and nonintegral slopes give infinity and character one;
the integral case uses the original reduced addition coordinates.
-/

@[expose] public section
namespace FLT.Mazur
open IsLocalRing WeierstrassCurve
variable {K : Type*} [Field K] [DecidableEq K] {A : ValuationSubring K}
  {W : WeierstrassCurve A} {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  [DecidableEq (ResidueField A)]

include D in
omit [DecidableEq (ResidueField A)] in
/-- Cancelling equal depths in the generic slope identity requires no integral slope. -/
theorem node_equal_depth_field_slope_identity (k : ℕ) (a b c d : A)
    (h₁ : (W.map (algebraMap A K)).toAffine.Equation
      ((π ^ k * a : A) : K) ((π ^ k * b : A) : K))
    (h₂ : (W.map (algebraMap A K)).toAffine.Equation
      ((π ^ k * c : A) : K) ((π ^ k * d : A) : K))
    (hxy : ¬ (((π ^ k * a : A) : K) = ((π ^ k * c : A) : K) ∧
      ((π ^ k * b : A) : K) = (W.map (algebraMap A K)).toAffine.negY
        ((π ^ k * c : A) : K) ((π ^ k * d : A) : K))) :
    ((a : K) - c) * (W.map (algebraMap A K)).toAffine.slope
      ((π ^ k * a : A) : K) ((π ^ k * c : A) : K)
      ((π ^ k * b : A) : K) ((π ^ k * d : A) : K) = (b : K) - d := by
  have he := (slope_cleared_identities _ h₁ h₂ hxy).1
  have hn : (π : K) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr D.uniformizer_ne_zero
  apply mul_left_cancel₀ (pow_ne_zero k hn)
  push_cast at he
  linear_combination he

/-- The actual smooth output has the opposite character law, including infinity. -/
theorem node_opposite_reduction_character (k : ℕ) (hk : 0 < k) (a b c d : A)
    (h₁ : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((π ^ k * a : A) : K) ((π ^ k * b : A) : K))
    (h₂ : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((π ^ k * c : A) : K) ((π ^ k * d : A) : K))
    (ha : IsUnit a) (hb : b ∈ maximalIdeal A) (hd : IsUnit d)
    (hdt : d + W.a₁ * c ∈ maximalIdeal A)
    (q : (W.map (residue A)).toAffine.Point)
    (hq : ReducesTo A W (.some _ _ h₁ + .some _ _ h₂) q) :
    residue A d * (Additive.toMul (splitDepthResidueCharacter D q)).val =
      -residue A (b + W.a₁ * a) := by
  have hinf (he : q = 0) (hac : residue A a = residue A c) :
      residue A d * (Additive.toMul (splitDepthResidueCharacter D q)).val =
        -residue A (b + W.a₁ * a) := by
    rw [he, (splitDepthResidueCharacter_eq_one_iff D 0).mpr rfl, Units.val_one, mul_one]
    exact node_opposite_equal_horizontal_character W hb hdt hac
  by_cases hxy : ((π ^ k * a : A) : K) = ((π ^ k * c : A) : K) ∧
      ((π ^ k * b : A) : K) = (W.map (algebraMap A K)).toAffine.negY
        ((π ^ k * c : A) : K) ((π ^ k * d : A) : K)
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2] at hq
    apply hinf ((reducesTo_zero A W).unique A W hq).symm
    apply congrArg (residue A)
    exact mul_left_cancel₀ (pow_ne_zero k D.uniformizer_ne_zero) (Subtype.ext hxy.1)
  let l := (W.map (algebraMap A K)).toAffine.slope
    ((π ^ k * a : A) : K) ((π ^ k * c : A) : K)
    ((π ^ k * b : A) : K) ((π ^ k * d : A) : K)
  by_cases hl : l ∈ A
  · exact node_integral_opposite_reduction_character D k hk a b c d ⟨l, hl⟩
      h₁ h₂ ha hb hd hdt hxy rfl q hq
  · have hz : ReducesTo A W (.some _ _ h₁ + .some _ _ h₂) 0 := by
      rw [Affine.Point.add_some hxy]
      apply reducesTo_of_nonintegral
      intro hx
      exact hl (slope_mem_of_addX_mem A W (π ^ k * a) (π ^ k * c) l hx)
    apply hinf (hq.unique A W hz)
    exact node_nonintegral_line_residue A
      (node_equal_depth_field_slope_identity D k a b c d h₁.1 h₂.1 hxy) hl

end FLT.Mazur
