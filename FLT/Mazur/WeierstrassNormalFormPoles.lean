/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassAffineNormalForm
public import FLT.Mazur.WeierstrassOriginWeightedPoles

/-!
# Coefficientwise pole bounds for the original normal form

The bound on p(x)+q(x)y is exactly the simultaneous weighted bound on its
nonzero coefficients. Even over a nonreduced base, no cancellation between
the even x weights and the odd y weights is possible.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The finite set of original normal-form monomials. -/
def originNormalSupport (p q : R[X]) : Finset (ℕ × ℕ) :=
  (p.support ×ˢ {0}) ∪ (q.support ×ˢ {1})

/-- The actual normal form is the corresponding finite sum of weighted monomials. -/
theorem affineNormalForm_eq_sum (p q : R[X]) :
    affineNormalForm W p q = ∑ k ∈ originNormalSupport p q,
      originPoleMonomial W (if k.2 = 0 then p.coeff k.1 else q.coeff k.1) k.1 k.2 := by
  classical
  have hd : Disjoint (p.support ×ˢ {0}) (q.support ×ˢ {1}) := by
    simp only [Finset.disjoint_left, Finset.mem_product, Finset.mem_singleton]
    intro k hk hk'
    omega
  simp only [originNormalSupport, Finset.sum_union hd, Finset.sum_product,
    Finset.sum_singleton, originPoleMonomial, ↓reduceIte, pow_zero, pow_one, mul_one]
  simp only [affineNormalForm, aeval_def, eval₂_eq_sum, sum_def, Finset.sum_mul,
    Nat.one_ne_zero, ↓reduceIte]

/-- A bound on the actual normal form detects each original polynomial coefficient. -/
theorem affineNormalForm_pole_iff (p q : R[X]) (n : ℕ) :
    HasOriginPoleBound W (affineNormalForm W p q) n ↔
      (∀ i, p.coeff i = 0 ∨ 2 * i ≤ n) ∧
      (∀ i, q.coeff i = 0 ∨ 2 * i + 3 ≤ n) := by
  classical
  rw [affineNormalForm_eq_sum]
  have hsep := originNormalWeight_injective (s := originNormalSupport p q) (by
    intro k hk
    simp only [originNormalSupport, Finset.mem_union, Finset.mem_product,
      Finset.mem_singleton] at hk
    rcases hk with hk | hk <;> omega)
  rw [originPole_sum_monomials_iff W _ _ hsep]
  constructor
  · intro h
    constructor
    · intro i
      by_cases hi : p.coeff i = 0
      · exact Or.inl hi
      · have hk : (i, 0) ∈ originNormalSupport p q := by
          simp [originNormalSupport, mem_support_iff, hi]
        simpa using h (i, 0) hk
    · intro i
      by_cases hi : q.coeff i = 0
      · exact Or.inl hi
      · have hk : (i, 1) ∈ originNormalSupport p q := by
          simp [originNormalSupport, mem_support_iff, hi]
        simpa using h (i, 1) hk
  · rintro ⟨hp, hq⟩ k hk
    simp only [originNormalSupport, Finset.mem_union, Finset.mem_product,
      Finset.mem_singleton] at hk
    rcases hk with hk | hk
    · simpa [hk.2] using hp k.1
    · simpa [hk.2] using hq k.1

end FLT.Mazur.WeierstrassIntegralChart
