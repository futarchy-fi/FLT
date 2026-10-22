/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# Combining exact equations modulo a fixed residual ideal

Independent chart corrections need not agree. Multiplication combines them
into one correction, at the cost of adding their exponents. This works over
arbitrary commutative rings, including nonreduced and non-Noetherian rings.
-/

@[expose] public section
namespace FLT.Mazur.FiniteIdealResidualPowers
open scoped BigOperators
variable {R : Type*} [CommRing R] {ι : Type*}

/-- Mixed terms in a product of two corrected equations remain in the residual ideal. -/
theorem mul_sup_le (I K J : Ideal R) :
    (I ⊔ J) * (K ⊔ J) ≤ I * K ⊔ J := by
  rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
  exact sup_le (sup_le le_sup_left (Ideal.mul_le_right.trans le_sup_right))
    (sup_le (Ideal.mul_le_left.trans le_sup_right)
      (Ideal.mul_le_left.trans le_sup_right))

/-- Multiplying finitely many independently corrected ideals gives one residual correction. -/
theorem prod_sup_le (s : Finset ι) (I : ι → Ideal R) (J : Ideal R) :
    (∏ i ∈ s, I i ⊔ J) ≤ (∏ i ∈ s, I i) ⊔ J := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (Ideal.mul_mono le_rfl ih).trans (mul_sup_le _ _ _)

/-- The sum of chart exponents gives exact membership in their intersection plus the residual. -/
theorem pow_sum_le_inf_sup (s : Finset ι) (I : ι → Ideal R) (J Q : Ideal R)
    (k : ι → ℕ) (h : ∀ i ∈ s, Q ^ k i ≤ I i ⊔ J) :
    Q ^ (∑ i ∈ s, k i) ≤ s.inf I ⊔ J := by
  have hp : (∏ i ∈ s, Q ^ k i) ≤ ∏ i ∈ s, I i ⊔ J := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      exact Ideal.mul_mono (h i (Finset.mem_insert_self i s))
        (ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj)))
  rw [Finset.prod_pow_eq_pow_sum] at hp
  exact hp.trans ((prod_sup_le s I J).trans (sup_le_sup_right Ideal.prod_le_inf J))

/-- A fixed exponent on all charts gives an explicit finite exponent on their intersection. -/
theorem pow_card_mul_le_inf_sup (s : Finset ι) (I : ι → Ideal R) (J Q : Ideal R)
    (k : ℕ) (h : ∀ i ∈ s, Q ^ k ≤ I i ⊔ J) :
    Q ^ (s.card * k) ≤ s.inf I ⊔ J := by
  simpa only [Finset.sum_const, smul_eq_mul] using
    pow_sum_le_inf_sup s I J Q (fun _ ↦ k) h

end FLT.Mazur.FiniteIdealResidualPowers
