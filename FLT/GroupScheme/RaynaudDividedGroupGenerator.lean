/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudDividedPowerSums

/-!
# The divided prime power of a group generator

For t = [a] - 1 the relation (1 + t)^p = 1 gives t^p = p z.
Additive evaluation of z is minus that of t: all terms of degree at least
two disappear. This computes the linear term without dividing in the ring.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.CharacterAverage

variable {R S F : Type*} [CommRing R] [CommRing S] [Algebra R S] [Field F]
  (p : ℕ) (hp : p.Prime) (e : F →+ S)

include hp

/-- A p-torsion group generator has divided power with negative linear term. -/
theorem dividedPower_generator (x : AddMonoidAlgebra R F)
    (hx : augmentation x = 0) (hpow : (x + 1) ^ p = 1) :
    ∃ z, x ^ p = (p : R) • z ∧ additiveEvaluation e z = -additiveEvaluation e x := by
  classical
  let z : AddMonoidAlgebra R F :=
    -∑ k ∈ Finset.Ioo 0 p, (p.choose k / p : ℕ) • x ^ k
  refine ⟨z, ?_, ?_⟩
  · have h := add_pow_prime_eq' hp x 1
    rw [hpow, one_pow] at h
    simp only [one_pow, mul_one] at h
    have hz : (p : R) • z =
        -(p : AddMonoidAlgebra R F) *
          ∑ k ∈ Finset.Ioo 0 p, x ^ k * (p.choose k / p : ℕ) := by
      simp [z, Algebra.smul_def, mul_comm]
    rw [hz]
    linear_combination -h
  · change additiveEvaluation e (-∑ k ∈ Finset.Ioo 0 p, _) = _
    rw [map_neg, map_sum]
    congr 1
    rw [Finset.sum_eq_single 1]
    · simp [Nat.choose_one_right, Nat.div_self hp.pos]
    · intro k hk hk1
      rw [map_nsmul, additiveEvaluation_pow_eq_zero e x hx k (by
        have := (Finset.mem_Ioo.mp hk).1
        omega), nsmul_zero]
    · intro h
      exact False.elim (h (Finset.mem_Ioo.mpr ⟨by omega, hp.one_lt⟩))

/-- The group-algebra element [a] - 1 satisfies the required p-torsion relation. -/
theorem dividedPower_single_sub_one [CharP F p] (a : F) :
    ∃ z : AddMonoidAlgebra R F,
      (AddMonoidAlgebra.single a 1 - 1) ^ p = (p : R) • z ∧
      additiveEvaluation e z = -e a := by
  obtain ⟨z, hz, he⟩ := dividedPower_generator (R := R) p hp e
    (AddMonoidAlgebra.single a 1 - 1) (by simp) (by
      simp [AddMonoidAlgebra.single_pow, nsmul_eq_mul, CharP.cast_eq_zero,
        ← AddMonoidAlgebra.one_def])
  refine ⟨z, hz, ?_⟩
  simpa [AddMonoidAlgebra.one_def] using he

end ThreeAdicPlan.CharacterAverage
