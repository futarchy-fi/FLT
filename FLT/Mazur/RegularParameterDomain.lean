/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RegularParameterIdeals
public import Mathlib.RingTheory.Filtration

/-!
# A Noetherian local ring with a regular parameter is a domain

An annihilator of a nonzero element lies in every power of the maximal ideal:
regularity permits division by the parameter at every step. Krull intersection
then makes the annihilator zero.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FCurve
open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- A regular generator of the maximal ideal rules out zero divisors. -/
theorem isDomain_of_regular_parameter (t : R) (hr : IsRegular t)
    (ht : maximalIdeal R = Ideal.span {t}) : IsDomain R := by
  have hann : ∀ (n : ℕ) (a b : R), b ≠ 0 → a * b = 0 → a ∈ maximalIdeal R ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro a b hb hab
      have ha : a ∈ maximalIdeal R := by
        by_contra h
        exact hb ((notMem_maximalIdeal.mp h).mul_right_eq_zero.mp hab)
      rw [ht] at ha
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
      have hcb : c * b = 0 := by
        apply hr.left
        change t * (c * b) = t * 0
        rw [mul_zero, ← mul_assoc, mul_comm t c, hc, hab]
      rw [pow_succ]
      rw [← hc]
      exact Ideal.mul_mem_mul (ih c b hb hcb) (ht ▸ Ideal.subset_span rfl)
  have hz : NoZeroDivisors R := ⟨by
    intro a b hab
    by_cases hb : b = 0
    · exact Or.inr hb
    · apply Or.inl
      have ha : a ∈ ⨅ n : ℕ, maximalIdeal R ^ n :=
        by simpa only [Ideal.mem_iInf] using fun n ↦ hann n a b hb hab
      rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top,
        Ideal.mem_bot] at ha⟩
  exact { hz with }

end FLT.Mazur.FCurve
