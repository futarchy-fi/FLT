/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeOppositeAddition

/-!
# Simple quadratic roots in the even double-root charts

The second cleared slope identity at every depth excludes a slope in the
maximal ideal over a simple residual x-root. Thus two points above that
root have smooth sum, including when they coincide.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] [DecidableEq K] (A : ValuationSubring K)
  (W : WeierstrassCurve A)

/-- Cancel π^(k+3) from the second slope identity in the even chart. -/
theorem doubleRoot_even_second_slope_identity {π : A} (hπ : π ≠ 0)
    (k : ℕ) (a b c d l e1 e2 e3 e4 : A)
    (h1 : W.a₁ = π * e1) (h2 : W.a₂ = π * e2)
    (h3 : W.a₃ = π ^ (k + 3) * e3) (h4 : W.a₄ = π ^ (k + 3) * e4)
    (h₁ : (W.map (algebraMap A K)).toAffine.Equation
      ((π ^ (k + 2) * a : A) : K) ((π ^ (k + 3) * b : A) : K))
    (h₂ : (W.map (algebraMap A K)).toAffine.Equation
      ((π ^ (k + 2) * c : A) : K) ((π ^ (k + 3) * d : A) : K))
    (hxy : ¬ (((π ^ (k + 2) * a : A) : K) = ((π ^ (k + 2) * c : A) : K) ∧
      ((π ^ (k + 3) * b : A) : K) = (W.map (algebraMap A K)).toAffine.negY
        ((π ^ (k + 2) * c : A) : K) ((π ^ (k + 3) * d : A) : K)))
    (hl : (W.map (algebraMap A K)).toAffine.slope
      ((π ^ (k + 2) * a : A) : K) ((π ^ (k + 2) * c : A) : K)
      ((π ^ (k + 3) * b : A) : K) ((π ^ (k + 3) * d : A) : K) = (l : K)) :
    (b + d + e1 * c + e3) * l =
      π ^ (k + 1) * (a ^ 2 + a * c + c ^ 2) + e2 * (a + c) + e4 - W.a₁ * b := by
  have he := (slope_cleared_identities _ h₁ h₂ hxy).2
  rw [hl] at he
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, ValuationSubring.algebraMap_apply] at he
  have hi : (π ^ (k + 3) * b + π ^ (k + 3) * d + W.a₁ * (π ^ (k + 2) * c) + W.a₃) * l =
      (π ^ (k + 2) * a) ^ 2 + (π ^ (k + 2) * a) * (π ^ (k + 2) * c) + (π ^ (k + 2) * c) ^ 2 +
        W.a₂ * (π ^ (k + 2) * a + π ^ (k + 2) * c) + W.a₄ -
          W.a₁ * (π ^ (k + 3) * b) := by exact_mod_cast he
  rw [h1, h2, h3, h4] at hi
  rw [h1]
  apply mul_left_cancel₀ (pow_ne_zero (k + 3) hπ)
  simp only [pow_add] at hi ⊢
  linear_combination hi

/-- Points above the same simple even quadratic root add smoothly, including doubling. -/
theorem smoothReduction_add_of_doubleRoot_even_same {π : A} (hπ : π ≠ 0)
    (hπm : π ∈ maximalIdeal A) (k : ℕ) (a b c d e1 e2 e3 e4 : A)
    (h1 : W.a₁ = π * e1) (h2 : W.a₂ = π * e2)
    (h3 : W.a₃ = π ^ (k + 3) * e3) (h4 : W.a₄ = π ^ (k + 3) * e4)
    (h6 : W.a₆ ∈ maximalIdeal A)
    (h₁ : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((π ^ (k + 2) * a : A) : K) ((π ^ (k + 3) * b : A) : K))
    (h₂ : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((π ^ (k + 2) * c : A) : K) ((π ^ (k + 3) * d : A) : K))
    (hac : residue A a = residue A c)
    (hd : 2 * residue A e2 * residue A a + residue A e4 ≠ 0) :
    SmoothReduction A W (Affine.Point.toProjective (.some _ _ h₁ + .some _ _ h₂)) := by
  by_cases hxy : ((π ^ (k + 2) * a : A) : K) = ((π ^ (k + 2) * c : A) : K) ∧
      ((π ^ (k + 3) * b : A) : K) = (W.map (algebraMap A K)).toAffine.negY
        ((π ^ (k + 2) * c : A) : K) ((π ^ (k + 3) * d : A) : K)
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
    exact smoothReduction_zero A W
  let l := (W.map (algebraMap A K)).toAffine.slope
    ((π ^ (k + 2) * a : A) : K) ((π ^ (k + 2) * c : A) : K)
    ((π ^ (k + 3) * b : A) : K) ((π ^ (k + 3) * d : A) : K)
  have hm (t : A) : π * t ∈ maximalIdeal A := (maximalIdeal A).mul_mem_right _ hπm
  have hpow (n : ℕ) (hn : n ≠ 0) (t : A) : π ^ n * t ∈ maximalIdeal A :=
    (maximalIdeal A).mul_mem_right _
      (Ideal.pow_le_self hn (Ideal.pow_mem_pow hπm n))
  have h10 : residue A W.a₁ = 0 := (residue_eq_zero_iff _).mpr (h1 ▸ hm e1)
  by_cases hl : l ∈ A
  · let u : A := ⟨l, hl⟩
    have he := doubleRoot_even_second_slope_identity A W hπ k a b c d u e1 e2 e3 e4
      h1 h2 h3 h4 h₁.1 h₂.1 hxy rfl
    have hu : residue A u ≠ 0 := by
      intro hz
      have hr := congrArg (residue A) he
      simp only [map_mul, map_add, map_sub, map_pow, hz, mul_zero, h10, zero_mul,
        sub_zero, ← hac, (residue_eq_zero_iff _).mpr hπm,
        zero_pow (by omega : k + 1 ≠ 0), zero_add] at hr
      apply hd
      linear_combination -hr
    apply smoothReduction_add_of_node_nontangent A W _ _ _ _ u h₁ h₂ hxy rfl
      (h2 ▸ hm e2) (h3 ▸ hpow _ (by omega) _)
      (h4 ▸ hpow _ (by omega) _) h6 (hpow _ (by omega) a) (hpow _ (by omega) c)
    simpa only [h10, neg_zero] using And.intro hu hu
  · rw [Affine.Point.add_some hxy]
    apply smoothReduction_of_nonintegral
    intro hi
    exact hl (slope_mem_of_addX_mem A W (π ^ (k + 2) * a) (π ^ (k + 2) * c) l hi.1)

end FLT.Mazur
