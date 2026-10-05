/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeOppositeAddition

/-!
# Distinct type IV residual labels add smoothly

If the divided y-coordinates are distinct modulo the maximal ideal, the
first cleared slope identity rules out a slope in that ideal. This gives
smooth reduction of the sum, including vertical and nonintegral slopes.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

/-- Singular points with different divided y-coordinates add into E₀. -/
theorem smoothReduction_add_of_typeIV_distinct {K : Type*} [Field K] [DecidableEq K]
    (A : ValuationSubring K) (W : WeierstrassCurve A) {π : A} (hπ : π ≠ 0)
    (hπm : π ∈ maximalIdeal A) (a b c d : A)
    (h₁ : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((π * a : A) : K) ((π * b : A) : K))
    (h₂ : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((π * c : A) : K) ((π * d : A) : K))
    (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ ∈ maximalIdeal A)
    (h3 : W.a₃ ∈ maximalIdeal A) (h4 : W.a₄ ∈ maximalIdeal A)
    (h6 : W.a₆ ∈ maximalIdeal A) (hbd : residue A b ≠ residue A d) :
    SmoothReduction A W (Affine.Point.toProjective (.some _ _ h₁ + .some _ _ h₂)) := by
  by_cases hxy : ((π * a : A) : K) = ((π * c : A) : K) ∧
      ((π * b : A) : K) = (W.map (algebraMap A K)).toAffine.negY
        ((π * c : A) : K) ((π * d : A) : K)
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
    exact smoothReduction_zero A W
  let l := (W.map (algebraMap A K)).toAffine.slope
    ((π * a : A) : K) ((π * c : A) : K) ((π * b : A) : K) ((π * d : A) : K)
  by_cases hl : l ∈ A
  · let u : A := ⟨l, hl⟩
    have he := node_equal_depth_slope_identity A W hπ 1 a b c d u
      (by simpa using h₁.1) (by simpa using h₂.1) (by simpa using hxy)
      (by simpa only [pow_one] using (show l = (u : K) from rfl))
    have hu : residue A u ≠ 0 := by
      intro hz
      have hr := congrArg (residue A) he
      simp only [map_mul, map_sub, hz, mul_zero] at hr
      exact hbd (sub_eq_zero.mp hr.symm)
    apply smoothReduction_add_of_node_nontangent A W _ _ _ _ u h₁ h₂ hxy rfl
      h2 h3 h4 h6 ((maximalIdeal A).mul_mem_right _ hπm)
      ((maximalIdeal A).mul_mem_right _ hπm)
    simpa only [(residue_eq_zero_iff _).mpr h1, neg_zero] using And.intro hu hu
  · rw [Affine.Point.add_some hxy]
    apply smoothReduction_of_nonintegral
    intro hi
    exact hl (slope_mem_of_addX_mem A W (π * a) (π * c) l hi.1)

end FLT.Mazur
