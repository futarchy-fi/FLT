/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFreeAdicComplete
public import FLT.Mathlib.RingTheory.AdicCompletion.Power
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Completeness of finite DVR extensions

The extended maximal ideal is a positive power of the larger maximal ideal.
Finite free completeness and the cofinality of these powers give completeness
without requiring the extension to be unramified.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]

/-- The extended base maximal ideal is a positive power of the larger maximal ideal. -/
theorem finiteDvr_maximalIdeal_power :
    ∃ e : ℕ, 0 < e ∧ (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ^ e := by
  have hn : (maximalIdeal R).map (algebraMap R S) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot (IsDiscreteValuationRing.not_a_field R)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hn hπ
  rw [← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq] at he
  refine ⟨e, ?_, he⟩
  have hle : (maximalIdeal R).map (algebraMap R S) ≤ maximalIdeal S := by
    rw [Ideal.map_le_iff_le_comap, maximalIdeal_comap]
  by_contra h
  have he0 : e = 0 := Nat.eq_zero_of_not_pos h
  rw [he, he0, pow_zero, Ideal.one_eq_top] at hle
  exact (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp hle)

/-- Every finite faithful DVR extension of a complete DVR is complete. -/
theorem finiteDvr_complete [IsAdicComplete (maximalIdeal R) R] :
    IsAdicComplete (maximalIdeal S) S := by
  let : Module.Free R S := inferInstance
  obtain ⟨e, he, hm⟩ := finiteDvr_maximalIdeal_power R S
  let : IsAdicComplete (maximalIdeal S ^ e) S := by
    rw [← hm]
    exact ThreeAdicPlan.adicComplete_finite_free_algebra (maximalIdeal R) S
  exact IsAdicComplete.ofPow _ he

end LocalClassFieldTheory
