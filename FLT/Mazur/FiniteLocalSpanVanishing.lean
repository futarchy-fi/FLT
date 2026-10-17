/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# What divisibility of a finite local error span requires

Over a local ring a finite span is maximal-ideal divisible precisely when
all of its specified generators vanish. Thus merely putting an error into a
cyclic finite submodule does not resolve its divisibility obligation.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteErrorReduction
variable {R M ι : Type*} [CommRing R] [IsLocalRing R]
  [AddCommGroup M] [Module R M] [Finite ι] (e : ι → M)

/-- Local divisibility of a finite specified span is equivalent to exact generator vanishing. -/
theorem finite_span_local_divisible_iff :
    Submodule.span R (Set.range e) ≤
      IsLocalRing.maximalIdeal R • Submodule.span R (Set.range e) ↔
        ∀ j, e j = 0 := by
  constructor
  · intro h
    have hz := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
      (IsLocalRing.maximalIdeal R) (Submodule.span R (Set.range e))
      (Submodule.fg_span (Set.finite_range e)) h (IsLocalRing.maximalIdeal_le_jacobson _)
    intro j
    have hj := Submodule.subset_span (R := R) (Set.mem_range_self (f := e) j)
    rw [hz] at hj
    exact hj
  · intro h
    have hz : Submodule.span R (Set.range e) = ⊥ := by
      apply le_bot_iff.mp
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact h j
    rw [hz]
    exact bot_le

/-- Enlarging the finite container cannot bypass exact vanishing of a contained error. -/
theorem exists_finite_local_divisible_container_iff (x : M) :
    (∃ Q : Submodule R M, Q.FG ∧ Q ≤ IsLocalRing.maximalIdeal R • Q ∧ x ∈ Q) ↔
      x = 0 := by
  constructor
  · rintro ⟨Q, hQ, hred, hx⟩
    have hz := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
      (IsLocalRing.maximalIdeal R) Q hQ hred (IsLocalRing.maximalIdeal_le_jacobson _)
    rwa [hz, Submodule.mem_bot] at hx
  · rintro rfl
    exact ⟨⊥, Submodule.fg_bot, bot_le, Submodule.zero_mem _⟩

end FLT.Mazur.FiniteErrorReduction
