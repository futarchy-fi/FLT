/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Transporting original ideal powers through a completion comparison

Finite evaluation kernels recover the extended original ideal powers.
An equivalence preserving these kernels therefore transports the filtration.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicCompletionFiltrationTransport

variable {A B : Type*} [CommRing A] [CommRing B]
  (I : Ideal A) (J : Ideal B)

/-- Ring and module evaluations vanish on exactly the same completed elements. -/
theorem eval_zero_iff (n : ℕ) (x : AdicCompletion I A) :
    AdicCompletion.evalₐ I n x = 0 ↔ AdicCompletion.eval I A n x = 0 := by
  constructor
  · intro h
    rw [← AdicCompletion.factor_evalₐ_eq_eval I x (by simp), h, map_zero]
  · intro h
    rw [← AdicCompletion.factor_eval_eq_evalₐ I x (by simp), h, map_zero]

/-- The extension of every original ideal power is its finite evaluation kernel. -/
theorem mem_map_power_iff (hI : I.FG) (n : ℕ) (x : AdicCompletion I A) :
    x ∈ (I ^ n).map (algebraMap A (AdicCompletion I A)) ↔
      AdicCompletion.evalₐ I n x = 0 := by
  rw [eval_zero_iff]
  change x ∈ ((I ^ n).map (algebraMap A (AdicCompletion I A))).restrictScalars A ↔ _
  rw [← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval hI]
  rfl

/-- A finite-level kernel comparison transports the extended original ideal power. -/
theorem map_power (hI : I.FG) (hJ : J.FG)
    (e : AdicCompletion I A ≃+* AdicCompletion J B) (n : ℕ)
    (he : ∀ x, AdicCompletion.evalₐ J n (e x) = 0 ↔
      AdicCompletion.evalₐ I n x = 0) :
    ((I ^ n).map (algebraMap A (AdicCompletion I A))).map e.toRingHom =
      (J ^ n).map (algebraMap B (AdicCompletion J B)) := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective]
  constructor
  · rintro ⟨z, hz, hz'⟩
    have : z = x := e.injective hz'
    subst z
    exact (mem_map_power_iff J hJ n _).mpr ((he x).mpr
      ((mem_map_power_iff I hI n x).mp hz))
  · intro hx
    exact ⟨x, (mem_map_power_iff I hI n x).mpr
      ((he x).mp ((mem_map_power_iff J hJ n _).mp hx)), rfl⟩

end FLT.Mazur.AdicCompletionFiltrationTransport
