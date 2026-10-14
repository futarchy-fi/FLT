/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeIntegralMiddleCharacter

/-!
# Middle-depth characters through all slope charts

The second denominator controls vertical and nonintegral sums, which reduce
to infinity. Together with the integral chart this computes the actual
smooth-reduction character without an affine output hypothesis.
-/

@[expose] public section
namespace FLT.Mazur
open IsLocalRing WeierstrassCurve
variable {K : Type*} [Field K] [DecidableEq K] {A : ValuationSubring K}
  {W : WeierstrassCurve A} {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  [DecidableEq (ResidueField A)]

/-- The actual smooth output has the middle character law, including infinity. -/
theorem node_middle_reduction_character (k : ℕ) (hk : 0 < k) (hkn : k ≤ n) (a b c d : A)
    (h₁ : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((π ^ k * a : A) : K) ((π ^ k * b : A) : K))
    (h₂ : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((π ^ k * c : A) : K) ((π ^ k * d : A) : K))
    (hb : IsUnit b) (hd : IsUnit (d + W.a₁ * c))
    (q : (W.map (residue A)).toAffine.Point)
    (hq : ReducesTo A W (.some _ _ h₁ + .some _ _ h₂) q) :
    residue A b * (Additive.toMul (splitDepthResidueCharacter D q)).val =
      -residue A (d + W.a₁ * c) := by
  obtain ⟨e₃, he₃, h3⟩ := exists_node_deep_factor D.maximalIdeal_eq k
    (Ideal.pow_le_pow_right (by omega) D.a₃_mem)
  obtain ⟨e₄, _, h4⟩ := exists_node_deep_factor D.maximalIdeal_eq k
    (Ideal.pow_le_pow_right (by omega) D.a₄_mem)
  have hinf (he : q = 0) (hc : residue A b = -residue A (d + W.a₁ * c)) :
      residue A b * (Additive.toMul (splitDepthResidueCharacter D q)).val =
        -residue A (d + W.a₁ * c) := by
    rw [he, (splitDepthResidueCharacter_eq_one_iff D 0).mpr rfl, Units.val_one, mul_one]
    exact hc
  by_cases hxy : ((π ^ k * a : A) : K) = ((π ^ k * c : A) : K) ∧
      ((π ^ k * b : A) : K) = (W.map (algebraMap A K)).toAffine.negY
        ((π ^ k * c : A) : K) ((π ^ k * d : A) : K)
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2] at hq
    apply hinf ((reducesTo_zero A W).unique A W hq).symm
    exact node_exceptional_second_residue A W D.uniformizer_ne_zero k a b c d e₃ e₄
      he₃ h3 h4 h₁.1 h₂.1 (Or.inl hxy.2)
  let l := (W.map (algebraMap A K)).toAffine.slope
    ((π ^ k * a : A) : K) ((π ^ k * c : A) : K)
    ((π ^ k * b : A) : K) ((π ^ k * d : A) : K)
  by_cases hl : l ∈ A
  · exact node_integral_middle_reduction_character D k hk hkn a b c d ⟨l, hl⟩
      h₁ h₂ hb hd hxy rfl q hq
  · have hz : ReducesTo A W (.some _ _ h₁ + .some _ _ h₂) 0 := by
      rw [Affine.Point.add_some hxy]
      apply reducesTo_of_nonintegral
      intro hx
      exact hl (slope_mem_of_addX_mem A W (π ^ k * a) (π ^ k * c) l hx)
    apply hinf (hq.unique A W hz)
    exact node_exceptional_second_residue A W D.uniformizer_ne_zero k a b c d e₃ e₄
      he₃ h3 h4 h₁.1 h₂.1 (Or.inr hl)


end FLT.Mazur
