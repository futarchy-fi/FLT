/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticTypeIIIStarSlope
public import FLT.Mazur.EllipticStarDeepCoordinates
public import FLT.Mazur.EllipticNormalizedTypeIII

/-!
# The normalized type III* rational component bound

The coefficient depths (1,2,3,3,5), with a₄ outside m⁴, give actual
coordinates (π²x,π³y). The slope obstruction makes any two nonzero
components sum to zero, so E/E₀ is killed by two and has at most two elements.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  {π : A} (hπ : π ≠ 0) (hgen : maximalIdeal A = Ideal.span {π})
  (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ ∈ maximalIdeal A ^ 2)
  (h3 : W.a₃ ∈ maximalIdeal A ^ 3) (h4 : W.a₄ ∈ maximalIdeal A ^ 3)
  (h6 : W.a₆ ∈ maximalIdeal A ^ 5) (h4' : W.a₄ ∉ maximalIdeal A ^ 4)

include hπ hgen h1 h2 h3 h4 h6 h4'

/-- Any two actual points outside E₀ add into E₀ under the normalized type III* tests. -/
theorem smoothReduction_add_of_normalizedTypeIIIStar
    (P Q : (W.map (algebraMap A K)).toProjective.Point)
    (hP : ¬ SmoothReduction A W P) (hQ : ¬ SmoothReduction A W Q) :
    SmoothReduction A W (P + Q) := by
  classical
  obtain ⟨v⟩ := exists_starDeepCoordinates A W hπ hgen h1 h2 h3 h4 h6 P hP
  obtain ⟨w⟩ := exists_starDeepCoordinates A W hπ hgen h1 h2 h3 h4 h6 Q hQ
  have hπm : π ∈ maximalIdeal A := hgen ▸ Ideal.mem_span_singleton_self π
  have hm (n : ℕ) (a : A) : π ^ n * a ∈ maximalIdeal A ^ n :=
    (maximalIdeal A ^ n).mul_mem_right _ (Ideal.pow_mem_pow hπm n)
  have hs := smoothReduction_add_of_normalizedTypeIIIStar_affine A W
    (π ^ 2 * v.x) (π ^ 3 * v.y) (π ^ 2 * w.x) (π ^ 3 * w.y) v.nonsingular w.nonsingular
    h1 h2 h3 (Ideal.pow_le_self (by decide : 3 ≠ 0) h4)
    (Ideal.pow_le_self (by decide : 5 ≠ 0) h6) h4' (hm 2 _) (hm 3 _) (hm 2 _) (hm 3 _)
  rw [toProjective_add] at hs
  simpa only [v.represents, w.represents] using hs

/-- Every pair of nonzero rational components sums to zero under the type III* tests. -/
theorem component_add_eq_zero_of_normalizedTypeIIIStar (c d : EllipticComponentQuotient A W)
    (hc : c ≠ 0) (hd : d ≠ 0) : c + d = 0 := by
  obtain ⟨P, rfl⟩ := ellipticComponentHom_surjective A W c
  obtain ⟨Q, rfl⟩ := ellipticComponentHom_surjective A W d
  rw [← map_add, ellipticComponentHom_eq_zero]
  exact smoothReduction_add_of_normalizedTypeIIIStar A W hπ hgen h1 h2 h3 h4 h6 h4' P Q
    (fun h => hc ((ellipticComponentHom_eq_zero A W P).mpr h))
    (fun h => hd ((ellipticComponentHom_eq_zero A W Q).mpr h))

/-- The normalized type III* quotient is finite, is killed by two, and has order at most two. -/
theorem normalizedTypeIIIStar_components :
    Finite (EllipticComponentQuotient A W) ∧
      (∀ c : EllipticComponentQuotient A W, 2 • c = 0) ∧
      Nat.card (EllipticComponentQuotient A W) ≤ 2 := by
  have h := component_add_eq_zero_of_normalizedTypeIIIStar A W hπ hgen h1 h2 h3 h4 h6 h4'
  obtain ⟨hf, hc⟩ := finite_card_le_two_of_nonzero_add_eq_zero h
  refine ⟨hf, fun c => ?_, hc⟩
  by_cases h0 : c = 0
  · simp [h0]
  · rw [two_nsmul]
    exact h c c h0 h0

end FLT.Mazur
