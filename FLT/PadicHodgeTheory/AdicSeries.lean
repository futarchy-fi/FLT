/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.AdicRingFunctor

/-! # Summing series whose terms lie in successive ideal powers -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
open Finset AdicCompletion
variable {R : Type*} [CommRing R] (I : Ideal R)

/-- Successive ideal-power bounds make the partial sums an adic Cauchy sequence. -/
theorem adicSeries_isAdicCauchy (a : ℕ → R) (ha : ∀ n, a n ∈ I ^ n) :
    IsAdicCauchy I R (fun n ↦ ∑ k ∈ range n, a k) := by
  apply (isAdicCauchy_iff I R _).mpr
  intro n
  rw [SModEq.sub_mem]
  simpa only [sum_range_succ, sub_add_eq_sub_sub, sub_self, zero_sub,
    smul_eq_mul, Ideal.mul_top] using (I ^ n).neg_mem (ha n)

variable [IsAdicComplete I R]

/-- Completeness supplies a sum with every prescribed finite congruence. -/
theorem adicSeries_exists (a : ℕ → R) (ha : ∀ n, a n ∈ I ^ n) :
    ∃ x : R, ∀ n, (∑ k ∈ range n, a k) ≡ x [SMOD (I ^ n • ⊤ : Ideal R)] :=
  IsPrecomplete.prec' _ (adicSeries_isAdicCauchy I a ha)

/-- The actual sum obtained from completeness, with no summability assumption. -/
def adicSeries (a : ℕ → R) (ha : ∀ n, a n ∈ I ^ n) : R :=
  (adicSeries_exists I a ha).choose

/-- The sum retains all finite truncations. -/
theorem adicSeries_spec (a : ℕ → R) (ha : ∀ n, a n ∈ I ^ n) (n : ℕ) :
    (∑ k ∈ range n, a k) ≡ adicSeries I a ha [SMOD (I ^ n • ⊤ : Ideal R)] :=
  (adicSeries_exists I a ha).choose_spec n

/-- Separatedness makes the sum unique. -/
theorem adicSeries_unique (a : ℕ → R) (ha : ∀ n, a n ∈ I ^ n) (x : R)
    (hx : ∀ n, (∑ k ∈ range n, a k) ≡ x [SMOD (I ^ n • ⊤ : Ideal R)]) :
    adicSeries I a ha = x := by
  apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
  exact fun n ↦ (adicSeries_spec I a ha n).symm.trans (hx n)

/-- An ideal-preserving ring map preserves these sums. -/
theorem adicSeries_map (f : R →+* R) (hf : I ≤ I.comap f)
    (a : ℕ → R) (ha : ∀ n, a n ∈ I ^ n) :
    f (adicSeries I a ha) =
      adicSeries I (fun n ↦ f (a n)) (fun n ↦ adicRing_pow_le I f hf n (ha n)) := by
  symm
  apply adicSeries_unique
  intro n
  have h := adicSeries_spec I a ha n
  rw [SModEq.sub_mem] at h ⊢
  simp only [smul_eq_mul, Ideal.mul_top] at h ⊢
  rw [← map_sum, ← map_sub]
  exact adicRing_pow_le I f hf n h

end PadicHodgeTheory
