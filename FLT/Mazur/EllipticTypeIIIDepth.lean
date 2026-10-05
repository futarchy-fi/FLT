/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNormalizedTypeIII

/-!
# The b₈ depth test for type III

The conventional b₈ test implies the a₄ test used by the actual component
bound. The ideal calculation works in every residue characteristic.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

/-- The error in replacing b₈ by -a₄² has depth at least three. -/
theorem b8_add_a4_sq_mem_cube {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    (I : Ideal R) (h1 : W.a₁ ∈ I) (h2 : W.a₂ ∈ I) (h3 : W.a₃ ∈ I)
    (h4 : W.a₄ ∈ I) (h6 : W.a₆ ∈ I ^ 2) : W.b₈ + W.a₄ ^ 2 ∈ I ^ 3 := by
  have hm {a b : R} (ha : a ∈ I) (hb : b ∈ I ^ 2) : a * b ∈ I ^ 3 := by
    simpa only [pow_succ', pow_one] using Ideal.mul_mem_mul ha hb
  have ht {a b c : R} (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I) :
      a * b * c ∈ I ^ 3 := by
    simpa only [pow_succ, pow_zero, one_mul] using Ideal.mul_mem_mul (Ideal.mul_mem_mul ha hb) hc
  have he : W.b₈ + W.a₄ ^ 2 = W.a₁ * (W.a₁ * W.a₆) +
      4 * (W.a₂ * W.a₆) - W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 := by
    rw [b₈]
    ring
  rw [he]
  exact (I ^ 3).add_mem ((I ^ 3).sub_mem
    ((I ^ 3).add_mem (hm h1 ((I ^ 2).mul_mem_left _ h6))
      ((I ^ 3).mul_mem_left _ (hm h2 h6))) (ht h1 h3 h4))
    (hm h2 (Ideal.pow_mem_pow h3 2))

/-- A shallow b₈ forces a shallow a₄ under the additive depth tests. -/
theorem a4_not_mem_square_of_b8_not_mem_cube {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (I : Ideal R)
    (h1 : W.a₁ ∈ I) (h2 : W.a₂ ∈ I) (h3 : W.a₃ ∈ I)
    (h4 : W.a₄ ∈ I) (h6 : W.a₆ ∈ I ^ 2) (h8 : W.b₈ ∉ I ^ 3) : W.a₄ ∉ I ^ 2 := by
  intro h
  apply h8
  have hs : W.a₄ ^ 2 ∈ I ^ 3 := by
    simpa only [pow_succ, pow_zero, one_mul] using Ideal.mul_mem_mul h h4
  simpa only [add_sub_cancel_right] using
    (I ^ 3).sub_mem (b8_add_a4_sq_mem_cube W I h1 h2 h3 h4 h6) hs

/-- The conventional type III b₈ test bounds the actual component quotient by two. -/
theorem typeIII_b8_components {K : Type*} [Field K] (A : ValuationSubring K)
    (W : WeierstrassCurve A)
    (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ ∈ maximalIdeal A)
    (h3 : W.a₃ ∈ maximalIdeal A) (h4 : W.a₄ ∈ maximalIdeal A)
    (h6 : W.a₆ ∈ maximalIdeal A ^ 2) (h8 : W.b₈ ∉ maximalIdeal A ^ 3) :
    Finite (EllipticComponentQuotient A W) ∧
      (∀ c : EllipticComponentQuotient A W, 2 • c = 0) ∧
      Nat.card (EllipticComponentQuotient A W) ≤ 2 :=
  normalizedTypeIII_components A W h1 h2 h3 h4 (Ideal.pow_le_self (by decide) h6)
    (a4_not_mem_square_of_b8_not_mem_cube W _ h1 h2 h3 h4 h6 h8)

end FLT.Mazur
