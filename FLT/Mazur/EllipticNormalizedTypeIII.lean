/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticTypeIIISlope
public import FLT.Mazur.EllipticSingularPointChart
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The normalized type III rational component bound

When every coefficient lies in the maximal ideal and a₄ does not lie in
its square, any two points outside E₀ add into E₀. Thus the actual rational
component quotient has at most two elements. This is a coefficient branch,
not an assertion that arbitrary additive models satisfy these tests.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

/-- A group whose nonzero elements pairwise add to zero has at most two elements. -/
theorem finite_card_le_two_of_nonzero_add_eq_zero {G : Type*} [AddGroup G]
    (h : ∀ c d : G, c ≠ 0 → d ≠ 0 → c + d = 0) : Finite G ∧ Nat.card G ≤ 2 := by
  classical
  have hs (c d : G) (hc : c ≠ 0) (hd : d ≠ 0) : c = d := by
    have hcd := eq_neg_of_add_eq_zero_left (h c d hc hd)
    have hdd := eq_neg_of_add_eq_zero_left (h d d hd hd)
    exact hcd.trans hdd.symm
  let f : G → Bool := fun c => decide (c = 0)
  have hf : Function.Injective f := by
    intro c d he
    by_cases hc : c = 0
    · by_cases hd : d = 0
      · exact hc.trans hd.symm
      · simp [f, hc, hd] at he
    · by_cases hd : d = 0
      · simp [f, hc, hd] at he
      · exact hs c d hc hd
  exact ⟨Finite.of_injective f hf, by simpa using Nat.card_le_card_of_injective f hf⟩

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ ∈ maximalIdeal A)
  (h3 : W.a₃ ∈ maximalIdeal A) (h4 : W.a₄ ∈ maximalIdeal A)
  (h6 : W.a₆ ∈ maximalIdeal A) (h4' : W.a₄ ∉ maximalIdeal A ^ 2)

include h1 h2 h3 h4 h6 h4'

/-- Any two actual points outside E₀ add into E₀ under the normalized type III tests. -/
theorem smoothReduction_add_of_normalizedTypeIII
    (P Q : (W.map (algebraMap A K)).toProjective.Point)
    (hP : ¬ SmoothReduction A W P) (hQ : ¬ SmoothReduction A W Q) :
    SmoothReduction A W (P + Q) := by
  classical
  obtain ⟨x₁, y₁, hn₁, hx₁, hy₁, rfl⟩ := exists_singular_integral_affine A W h3 h4 h6 P hP
  obtain ⟨x₂, y₂, hn₂, hx₂, hy₂, rfl⟩ := exists_singular_integral_affine A W h3 h4 h6 Q hQ
  change SmoothReduction A W
    ((Projective.Point.toAffineAddEquiv _).symm (.some _ _ hn₁) +
      (Projective.Point.toAffineAddEquiv _).symm (.some _ _ hn₂))
  rw [← map_add]
  exact smoothReduction_add_of_normalizedTypeIII_affine A W x₁ y₁ x₂ y₂ hn₁ hn₂
    h1 h2 h3 h4 h6 h4' hx₁ hy₁ hx₂ hy₂

/-- Every pair of nonzero rational components sums to zero under the type III tests. -/
theorem component_add_eq_zero_of_normalizedTypeIII (c d : EllipticComponentQuotient A W)
    (hc : c ≠ 0) (hd : d ≠ 0) : c + d = 0 := by
  obtain ⟨P, rfl⟩ := ellipticComponentHom_surjective A W c
  obtain ⟨Q, rfl⟩ := ellipticComponentHom_surjective A W d
  rw [← map_add, ellipticComponentHom_eq_zero]
  exact smoothReduction_add_of_normalizedTypeIII A W h1 h2 h3 h4 h6 h4' P Q
    (fun h => hc ((ellipticComponentHom_eq_zero A W P).mpr h))
    (fun h => hd ((ellipticComponentHom_eq_zero A W Q).mpr h))

/-- The normalized type III quotient is finite, is killed by two, and has order at most two. -/
theorem normalizedTypeIII_components :
    Finite (EllipticComponentQuotient A W) ∧
      (∀ c : EllipticComponentQuotient A W, 2 • c = 0) ∧
      Nat.card (EllipticComponentQuotient A W) ≤ 2 := by
  have h := component_add_eq_zero_of_normalizedTypeIII A W h1 h2 h3 h4 h6 h4'
  obtain ⟨hf, hc⟩ := finite_card_le_two_of_nonzero_add_eq_zero h
  refine ⟨hf, fun c => ?_, hc⟩
  by_cases h0 : c = 0
  · simp [h0]
  · rw [two_nsmul]
    exact h c c h0 h0

end FLT.Mazur
