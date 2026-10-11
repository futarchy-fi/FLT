/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Kernels of finite-order evaluation on a completed ring

For a finite ideal, the nth evaluation kernel is the extension of its nth
power. Original elements therefore approximate completed elements modulo
precisely the powers of the extended ideal.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicEvaluationKernel

open AdicCompletion

set_option backward.isDefEq.respectTransparency false

variable {A : Type*} [CommRing A] (I : Ideal A) (hI : I.FG)

include hI

/-- The evaluation kernel is exactly the extended original ideal power. -/
theorem ker_eval (n : ℕ) : RingHom.ker (evalₐ I n).toRingHom =
    (I ^ n).map (algebraMap A (AdicCompletion I A)) := by
  apply Submodule.restrictScalars_injective A
  rw [← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval hI]
  ext x
  change evalₐ I n x = 0 ↔ eval I A n x = 0
  let h : (I ^ n • ⊤ : Ideal A) = I ^ n := by simp
  change Ideal.quotientEquivAlgOfEq A h (eval I A n x) = 0 ↔ _
  exact map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq A h).injective

/-- Every completed element admits an original representative to any prescribed finite order. -/
theorem exists_sub_mem (n : ℕ) (x : AdicCompletion I A) :
    ∃ a : A, x - AdicCompletion.of I A a ∈
      (I.map (algebraMap A (AdicCompletion I A))) ^ n := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
  refine ⟨a, ?_⟩
  rw [← Ideal.map_pow, ← ker_eval I hI]
  change evalₐ I n (x - AdicCompletion.of I A a) = 0
  rw [map_sub, ← ha]
  exact sub_self _

end FLT.Mazur.AdicEvaluationKernel
