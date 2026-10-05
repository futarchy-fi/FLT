/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeOppositeAddition

/-!
# The type III* slope obstruction

With x-coordinates in m² and y-coordinates in m³, a slope in m would
force a₄ into m⁴ by the second cleared slope identity. Exact depth three
of a₄ therefore makes every sum of two such points reduce smoothly.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

/-- Deeper coordinate depths rule out a slope in I when a₄ is outside I⁴. -/
theorem typeIIIStar_slope_not_mem {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    (I : Ideal R) {x₁ y₁ x₂ y₂ l : R}
    (h1 : W.a₁ ∈ I) (h2 : W.a₂ ∈ I ^ 2) (h3 : W.a₃ ∈ I ^ 3) (h4 : W.a₄ ∉ I ^ 4)
    (hx₁ : x₁ ∈ I ^ 2) (hy₁ : y₁ ∈ I ^ 3) (hx₂ : x₂ ∈ I ^ 2) (hy₂ : y₂ ∈ I ^ 3)
    (he : (y₁ + y₂ + W.a₁ * x₂ + W.a₃) * l =
      x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁) :
    l ∉ I := by
  intro hl
  apply h4
  have hm22 {a b : R} (ha : a ∈ I ^ 2) (hb : b ∈ I ^ 2) : a * b ∈ I ^ 4 := by
    simpa only [← pow_add] using Ideal.mul_mem_mul ha hb
  have hm13 {a b : R} (ha : a ∈ I) (hb : b ∈ I ^ 3) : a * b ∈ I ^ 4 := by
    simpa only [pow_succ'] using Ideal.mul_mem_mul ha hb
  have hm31 {a b : R} (ha : a ∈ I ^ 3) (hb : b ∈ I) : a * b ∈ I ^ 4 := by
    simpa only [pow_succ] using Ideal.mul_mem_mul ha hb
  have hx : W.a₁ * x₂ ∈ I ^ 3 := by
    simpa only [pow_succ'] using Ideal.mul_mem_mul h1 hx₂
  have ht : (y₁ + y₂ + W.a₁ * x₂ + W.a₃) * l ∈ I ^ 4 :=
    hm31 ((I ^ 3).add_mem ((I ^ 3).add_mem ((I ^ 3).add_mem hy₁ hy₂) hx) h3) hl
  have hr : x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) ∈ I ^ 4 :=
    (I ^ 4).add_mem ((I ^ 4).add_mem
      ((I ^ 4).add_mem (by simpa only [← pow_mul] using Ideal.pow_mem_pow hx₁ 2)
        (hm22 hx₁ hx₂)) (by simpa only [← pow_mul] using Ideal.pow_mem_pow hx₂ 2))
      (hm22 h2 ((I ^ 2).add_mem hx₁ hx₂))
  have ha : W.a₄ = (y₁ + y₂ + W.a₁ * x₂ + W.a₃) * l -
      (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂)) + W.a₁ * y₁ := by
    linear_combination -he
  rw [ha]
  exact (I ^ 4).add_mem ((I ^ 4).sub_mem ht hr) (hm13 h1 hy₁)

variable {K : Type*} [Field K] [DecidableEq K] (A : ValuationSubring K)
  (W : WeierstrassCurve A)

/-- Two affine points reducing to the cusp add to a smoothly reducing point in type III*. -/
theorem smoothReduction_add_of_normalizedTypeIIIStar_affine (x₁ y₁ x₂ y₂ : A)
    (h₁ : (W.map (algebraMap A K)).toAffine.Nonsingular (x₁ : K) (y₁ : K))
    (h₂ : (W.map (algebraMap A K)).toAffine.Nonsingular (x₂ : K) (y₂ : K))
    (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ ∈ maximalIdeal A ^ 2)
    (h3 : W.a₃ ∈ maximalIdeal A ^ 3) (h4 : W.a₄ ∈ maximalIdeal A)
    (h6 : W.a₆ ∈ maximalIdeal A) (h4' : W.a₄ ∉ maximalIdeal A ^ 4)
    (hx₁ : x₁ ∈ maximalIdeal A ^ 2) (hy₁ : y₁ ∈ maximalIdeal A ^ 3)
    (hx₂ : x₂ ∈ maximalIdeal A ^ 2) (hy₂ : y₂ ∈ maximalIdeal A ^ 3) :
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
      typeIIIStar_slope_not_mem W _ h1 h2 h3 h4' hx₁ hy₁ hx₂ hy₂ hi ((residue_eq_zero_iff _).mp h)
    apply smoothReduction_add_of_node_nontangent A W x₁ y₁ x₂ y₂ u h₁ h₂ hxy rfl
      (Ideal.pow_le_self (by decide : 2 ≠ 0) h2)
      (Ideal.pow_le_self (by decide : 3 ≠ 0) h3) h4 h6
      (Ideal.pow_le_self (by decide : 2 ≠ 0) hx₁)
      (Ideal.pow_le_self (by decide : 2 ≠ 0) hx₂)
    simpa only [(residue_eq_zero_iff _).mpr h1, neg_zero] using And.intro hu hu
  · rw [Affine.Point.add_some hxy]
    apply smoothReduction_of_nonintegral
    intro hi
    exact hl (slope_mem_of_addX_mem A W x₁ x₂ l hi.1)

end FLT.Mazur
