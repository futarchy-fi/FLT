/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Regular.AssociatedPrimeQuotient
public import FLT.Mathlib.RingTheory.Regular.QuotientDepth

/-! # Regular-sequence length is bounded by the dimension of every associated prime -/

@[expose] public section

universe u

namespace RingTheory.Sequence

variable {R M : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- A regular sequence gives a chain of primes starting at any associated prime. -/
theorem IsRegular.exists_prime_chain {rs : List R} (hreg : IsRegular M rs)
    {p : Ideal R} (hp : IsAssociatedPrime p M) :
    ∃ c : LTSeries (PrimeSpectrum R), c.head.asIdeal = p ∧ c.length = rs.length := by
  induction rs generalizing M p with
  | nil => exact ⟨.singleton _ ⟨p, hp.isPrime⟩, rfl, rfl⟩
  | cons x rs ih =>
    obtain ⟨hx, hrs⟩ := (isRegular_cons_iff M x rs).mp hreg
    obtain ⟨q, hq, hpq⟩ := exists_associatedPrime_quotSMulTop_gt hp hx
      (hreg.mem_maximalIdeal List.mem_cons_self)
    obtain ⟨c, hc, hlen⟩ := ih hrs hq
    have hpc : (⟨p, hp.isPrime⟩ : PrimeSpectrum R) < c.head := by
      change p < c.head.asIdeal
      rwa [hc]
    exact ⟨c.cons ⟨p, hp.isPrime⟩ hpc, by simp, by simp [hlen]⟩

/-- The depth of a finite local module is no larger than the dimension at an associated prime. -/
theorem IsRegular.length_le_dimension_quotient_associatedPrime {rs : List R}
    (hreg : IsRegular M rs) {p : Ideal R} (hp : IsAssociatedPrime p M) :
    (rs.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  obtain ⟨c, hc, hlen⟩ := hreg.exists_prime_chain hp
  let d : LTSeries (PrimeSpectrum.zeroLocus (R := R) p) := {
    length := c.length
    toFun := fun i ↦ ⟨c i, by
      change p ≤ (c i).asIdeal
      rw [← hc]
      exact c.monotone (Fin.zero_le i)⟩
    step := fun i ↦ c.step i
  }
  have h := Order.LTSeries.length_le_krullDim d
  rw [← Order.krullDim_eq_of_orderIso (Ideal.primeSpectrumQuotientOrderIsoZeroLocus p)] at h
  simpa only [d, hlen, ringKrullDim] using h

end RingTheory.Sequence
