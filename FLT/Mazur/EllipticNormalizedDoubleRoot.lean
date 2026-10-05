/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticDoubleRootEvenBound
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Exhausting the double-root iteration

Failure of both terminal tests forces a₃ and a₄ into arbitrarily high
powers of the maximal ideal. Adic separatedness makes both zero; together
with a₆ = 0 this contradicts generic ellipticity. In particular the
iteration terminates over a DVR and the actual component quotient has
order at most four.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

/-- Adic separatedness exhausts all double-root stages and bounds the actual quotient. -/
theorem normalizedDoubleRoot_components {K : Type*} [Field K]
    (A : ValuationSubring K) (W : WeierstrassCurve A)
    [IsHausdorff (maximalIdeal A) A] [(W.map (algebraMap A K)).IsElliptic]
    {π : A} (hπ : π ≠ 0) (hgen : maximalIdeal A = Ideal.span {π})
    (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ ∈ maximalIdeal A)
    (h2' : W.a₂ ∉ maximalIdeal A ^ 2)
    (h3 : W.a₃ ∈ maximalIdeal A ^ 2) (h4 : W.a₄ ∈ maximalIdeal A ^ 3)
    (h6 : W.a₆ = 0) :
    Finite (EllipticComponentQuotient A W) ∧ Nat.card (EllipticComponentQuotient A W) ≤ 4 := by
  classical
  obtain ⟨e2, he2⟩ := exists_node_coordinate_factor hgen 1 (by simpa using h2)
  simp only [pow_one] at he2
  have he2m : e2 ∉ maximalIdeal A := by
    intro hm
    apply h2'
    rw [he2, pow_two]
    exact Ideal.mul_mem_mul (hgen ▸ Ideal.mem_span_singleton_self π) hm
  by_contra hb
  have hdepth (k : ℕ) : W.a₃ ∈ maximalIdeal A ^ (k + 2) ∧
      W.a₄ ∈ maximalIdeal A ^ (k + 3) := by
    induction k with
    | zero => exact ⟨h3, h4⟩
    | succ k ih =>
      have h3' : W.a₃ ∈ maximalIdeal A ^ (k + 3) := by
        by_contra hn
        exact hb (normalizedDoubleRoot_odd_components A W hπ hgen e2 h1 he2 he2m
          k ih.1 hn ih.2 h6)
      have h4' : W.a₄ ∈ maximalIdeal A ^ (k + 4) := by
        by_contra hn
        exact hb (normalizedDoubleRoot_even_components A W hπ hgen e2 h1 he2 he2m
          k h3' ih.2 hn h6)
      exact ⟨h3', h4'⟩
  have hz (x : A) (hx : ∀ n : ℕ, x ∈ maximalIdeal A ^ n) : x = 0 := by
    apply IsHausdorff.haus' (I := maximalIdeal A)
    intro n
    simpa only [SModEq.zero, smul_eq_mul, ← Ideal.one_eq_top, mul_one] using hx n
  have h30 : W.a₃ = 0 := hz _ fun n =>
    Ideal.pow_le_pow_right (by omega : n ≤ n + 2) (hdepth n).1
  have h40 : W.a₄ = 0 := hz _ fun n =>
    Ideal.pow_le_pow_right (by omega : n ≤ n + 3) (hdepth n).2
  have hΔ : W.Δ = 0 := by simp [Δ, b₄, b₆, b₈, h30, h40, h6]
  apply (W.map (algebraMap A K)).isUnit_Δ.ne_zero
  rw [map_Δ, hΔ, map_zero]

end FLT.Mazur
