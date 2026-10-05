/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeOppositeAddition

/-!
# The slope obstruction in the normalized type III branch

When all coefficients vanish in the residue field and a₄ has exact order
one, a line through two points above the cusp cannot have slope in the
maximal ideal. Its sum therefore reduces smoothly, in every residue
characteristic. The argument includes doubling and vertical lines.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

/-- The second cleared slope identity rules out a slope in I when a₄ is not in I². -/
theorem typeIII_slope_not_mem {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    (I : Ideal R) {x₁ y₁ x₂ y₂ l : R}
    (h1 : W.a₁ ∈ I) (h2 : W.a₂ ∈ I) (h3 : W.a₃ ∈ I) (h4 : W.a₄ ∉ I ^ 2)
    (hx₁ : x₁ ∈ I) (hy₁ : y₁ ∈ I) (hx₂ : x₂ ∈ I) (hy₂ : y₂ ∈ I)
    (he : (y₁ + y₂ + W.a₁ * x₂ + W.a₃) * l =
      x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁) :
    l ∉ I := by
  intro hl
  apply h4
  have hm {a b : R} (ha : a ∈ I) (hb : b ∈ I) : a * b ∈ I ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul ha hb
  have ht : (y₁ + y₂ + W.a₁ * x₂ + W.a₃) * l ∈ I ^ 2 :=
    hm (I.add_mem (I.add_mem (I.add_mem hy₁ hy₂) (I.mul_mem_left _ hx₂)) h3) hl
  have hr : x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) ∈ I ^ 2 :=
    (I ^ 2).add_mem ((I ^ 2).add_mem
      ((I ^ 2).add_mem (Ideal.pow_mem_pow hx₁ 2) (hm hx₁ hx₂))
      (Ideal.pow_mem_pow hx₂ 2)) (hm h2 (I.add_mem hx₁ hx₂))
  have ha : W.a₄ = (y₁ + y₂ + W.a₁ * x₂ + W.a₃) * l -
      (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂)) + W.a₁ * y₁ := by
    linear_combination -he
  rw [ha]
  exact (I ^ 2).add_mem ((I ^ 2).sub_mem ht hr) (hm h1 hy₁)

variable {K : Type*} [Field K] [DecidableEq K] (A : ValuationSubring K)
  (W : WeierstrassCurve A)

/-- Two affine points reducing to the cusp add to a smoothly reducing point in type III. -/
theorem smoothReduction_add_of_normalizedTypeIII_affine (x₁ y₁ x₂ y₂ : A)
    (h₁ : (W.map (algebraMap A K)).toAffine.Nonsingular (x₁ : K) (y₁ : K))
    (h₂ : (W.map (algebraMap A K)).toAffine.Nonsingular (x₂ : K) (y₂ : K))
    (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ ∈ maximalIdeal A)
    (h3 : W.a₃ ∈ maximalIdeal A) (h4 : W.a₄ ∈ maximalIdeal A)
    (h6 : W.a₆ ∈ maximalIdeal A) (h4' : W.a₄ ∉ maximalIdeal A ^ 2)
    (hx₁ : x₁ ∈ maximalIdeal A) (hy₁ : y₁ ∈ maximalIdeal A)
    (hx₂ : x₂ ∈ maximalIdeal A) (hy₂ : y₂ ∈ maximalIdeal A) :
    SmoothReduction A W (Affine.Point.toProjective (.some _ _ h₁ + .some _ _ h₂)) := by
  by_cases hxy : (x₁ : K) = (x₂ : K) ∧
      (y₁ : K) = (W.map (algebraMap A K)).toAffine.negY (x₂ : K) (y₂ : K)
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
    exact smoothReduction_zero A W
  let l := (W.map (algebraMap A K)).toAffine.slope (x₁ : K) (x₂ : K) (y₁ : K) (y₂ : K)
  by_cases hl : l ∈ A
  · let u : A := ⟨l, hl⟩
    have he := (slope_cleared_identities _ h₁.1 h₂.1 hxy).2
    change _ * (u : K) = _ at he
    simp only [map_a₁, map_a₂, map_a₃, map_a₄, ValuationSubring.algebraMap_apply] at he
    have hi : (y₁ + y₂ + W.a₁ * x₂ + W.a₃) * u =
        x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁ := by
      exact_mod_cast he
    have hu : residue A u ≠ 0 := fun h =>
      typeIII_slope_not_mem W _ h1 h2 h3 h4' hx₁ hy₁ hx₂ hy₂ hi ((residue_eq_zero_iff _).mp h)
    apply smoothReduction_add_of_node_nontangent A W x₁ y₁ x₂ y₂ u h₁ h₂ hxy rfl
      h2 h3 h4 h6 hx₁ hx₂
    simpa only [(residue_eq_zero_iff _).mpr h1, neg_zero] using And.intro hu hu
  · rw [Affine.Point.add_some hxy]
    apply smoothReduction_of_nonintegral
    intro hi
    exact hl (slope_mem_of_addX_mem A W x₁ x₂ l hi.1)

end FLT.Mazur
