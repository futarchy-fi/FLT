/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-! # Finitely many ramified rational primes

The ramified rational primes of a number field divide its nonzero absolute
discriminant. This proves leaf G3 of `docs/CHEBOTAREV_PLAN.md` over `ℚ`.
-/

@[expose] public section

open NumberField

namespace Chebotarev

/-- Only finitely many rational primes ramify in a number field. -/
theorem finite_ramified_rational (L : Type*) [Field L] [NumberField L] :
    {q : ℕ | q.Prime ∧ ¬ Algebra.IsUnramifiedIn (𝓞 L)
      (Ideal.span {(q : ℤ)})}.Finite := by
  refine (NumberField.discr L).natAbs.primeFactors.finite_toSet.subset ?_
  rintro q ⟨hq, hram⟩
  have hdvd : (q : ℤ) ∣ NumberField.discr L := by
    by_contra h
    exact hram ((NumberField.not_dvd_discr_iff_isUnramifiedIn L (𝓞 L)
      (Nat.prime_iff_prime_int.mp hq)).mp h)
  exact Nat.mem_primeFactors.mpr
    ⟨hq, Int.natCast_dvd.mp hdvd, Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero L)⟩

end Chebotarev
