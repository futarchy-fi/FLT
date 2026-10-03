/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudAugmentationDerivation

/-!
# Divided prime powers of sums of augmentation elements

Mixed binomial terms have a factor p and lie in the square of the
augmentation ideal. Additive evaluation therefore removes their contribution
to the divided power.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.CharacterAverage

variable {R S F : Type*} [CommRing R] [CommRing S] [Algebra R S] [Field F]
  (p : ℕ) (hp : p.Prime) (e : F →+ S)

include hp in
/-- Adding augmentation elements adds the evaluated divided powers. -/
theorem dividedPower_add (x y z w : AddMonoidAlgebra R F)
    (hx : augmentation x = 0) (hy : augmentation y = 0)
    (hz : x ^ p = (p : R) • z) (hw : y ^ p = (p : R) • w) :
    ∃ t, (x + y) ^ p = (p : R) • t ∧
      additiveEvaluation e t = additiveEvaluation e z + additiveEvaluation e w := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp x y
  refine ⟨z + w + x * (y * r), ?_, ?_⟩
  · rw [hr, hz, hw]
    simp only [Algebra.smul_def, map_natCast]
    ring
  · rw [map_add, map_add,
      additiveEvaluation_mul_eq_zero e x (y * r) hx (by simp [hy]), add_zero]

include hp in
/-- Finite sums retain the sum of the evaluated divided powers. -/
theorem dividedPower_sum {ι : Type*} (s : Finset ι) (x z : ι → AddMonoidAlgebra R F)
    (hx : ∀ i ∈ s, augmentation (x i) = 0)
    (hz : ∀ i ∈ s, x i ^ p = (p : R) • z i) :
    ∃ t, (∑ i ∈ s, x i) ^ p = (p : R) • t ∧
      additiveEvaluation e t = ∑ i ∈ s, additiveEvaluation e (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp [hp.ne_zero], by simp⟩
  | @insert i s hi ih =>
    obtain ⟨t, ht, he⟩ := ih (fun j hj ↦ hx j (Finset.mem_insert_of_mem hj))
      (fun j hj ↦ hz j (Finset.mem_insert_of_mem hj))
    have hs : augmentation (∑ j ∈ s, x j) = 0 := by
      rw [map_sum]
      exact Finset.sum_eq_zero fun j hj ↦ hx j (Finset.mem_insert_of_mem hj)
    obtain ⟨w, hw, hew⟩ := dividedPower_add p hp e (x i) (∑ j ∈ s, x j) (z i) t
      (hx i (Finset.mem_insert_self i s)) hs (hz i (Finset.mem_insert_self i s)) ht
    exact ⟨w, by simpa [Finset.sum_insert hi] using hw,
      by simpa [Finset.sum_insert hi, he] using hew⟩

/-- Scaling an element scales its divided p-th power by the p-th power of the scalar. -/
theorem dividedPower_smul (r : R) (x z : AddMonoidAlgebra R F)
    (hz : x ^ p = (p : R) • z) : (r • x) ^ p = (p : R) • (r ^ p • z) := by
  rw [smul_pow, hz, smul_smul, smul_smul, mul_comm]

end ThreeAdicPlan.CharacterAverage
