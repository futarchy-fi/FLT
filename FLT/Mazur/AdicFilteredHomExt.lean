/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicEvaluationKernel
public import FLT.Mazur.AdicIdealFilteredMap

/-!
# Original elements determine filtered maps of completed algebras

Finite-order approximation and ideal-power compatibility prove uniqueness
of maps between completions from their values on the original algebra.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicFilteredHomExt

open AdicCompletion

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (I : Ideal A) (J : Ideal B)
  (f : AdicCompletion I A →ₐ[R] AdicCompletion J B)
  (hf : (I.map (algebraMap A (AdicCompletion I A))).map f.toRingHom ≤
    J.map (algebraMap B (AdicCompletion J B)))

include hf in
/-- A filtered map sends every source-ideal power into the corresponding evaluation kernel. -/
theorem eval_zero_of_mem (n : ℕ) (x : AdicCompletion I A)
    (hx : x ∈ (I.map (algebraMap A (AdicCompletion I A))) ^ n) :
    evalₐ J n (f x) = 0 := by
  have h := (pow_le_pow_left' hf n).trans (AdicIdealFilteredMap.pow_le_ker_eval J n)
  rw [← Ideal.map_pow] at h
  exact h (Ideal.mem_map_of_mem _ hx)

include hf in
/-- Original elements determine a filtered algebra map from a completion at a finite ideal. -/
theorem ext_of (hI : I.FG) (g : AdicCompletion I A →ₐ[R] AdicCompletion J B)
    (hg : (I.map (algebraMap A (AdicCompletion I A))).map g.toRingHom ≤
      J.map (algebraMap B (AdicCompletion J B)))
    (h : ∀ a, f (AdicCompletion.of I A a) = g (AdicCompletion.of I A a)) : f = g := by
  ext x : 1
  apply AdicCompletion.ext_evalₐ
  intro n
  obtain ⟨a, ha⟩ := AdicEvaluationKernel.exists_sub_mem I hI n x
  have hfx := eval_zero_of_mem I J f hf n _ ha
  have hgx := eval_zero_of_mem I J g hg n _ ha
  rw [map_sub, map_sub, sub_eq_zero] at hfx hgx
  rw [hfx, h, ← hgx]

end FLT.Mazur.AdicFilteredHomExt
