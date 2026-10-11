/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicDerivationCompletion
public import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Uniqueness of derivations on adic completions

When the ideal is finitely generated, every derivation to a completed
original module automatically loses at most one order of precision.
Consequently its values on original sections determine it uniquely.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicDerivationFiltration

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  (I : Ideal A) (hI : I.FG)

include hI

/-- Every derivation on the completion lowers the original filtration by at most one. -/
theorem eval_derivation_eq_zero
    (d : Derivation R (AdicCompletion I A) (AdicCompletion I M))
    (n : ℕ) {x : AdicCompletion I A} (hx : AdicCompletion.eval I A (n + 1) x = 0) :
    AdicCompletion.eval I M n (d x) = 0 := by
  have hx' : x ∈ (I.map (algebraMap A (AdicCompletion I A))) ^ (n + 1) := by
    rw [← Ideal.map_pow]
    change x ∈ ((I ^ (n + 1)).map (algebraMap A (AdicCompletion I A))).restrictScalars A
    rw [← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval hI]
    exact hx
  have hd := map_mem_pow_smul d (I.map (algebraMap A (AdicCompletion I A))) n hx'
  rw [← Ideal.map_pow] at hd
  change d x ∈ (((I ^ n).map (algebraMap A (AdicCompletion I A))) •
    (⊤ : Submodule (AdicCompletion I A) (AdicCompletion I M))).restrictScalars A at hd
  rw [Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top,
    AdicCompletion.pow_smul_top_eq_ker_eval hI] at hd
  exact hd

/-- Original sections determine a derivation with values in a completed original module. -/
theorem completion_ext
    (d e : Derivation R (AdicCompletion I A) (AdicCompletion I M))
    (h : ∀ a, d (AdicCompletion.of I A a) = e (AdicCompletion.of I A a)) : d = e := by
  ext x : 1
  apply AdicCompletion.ext
  intro n
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective
    (I ^ (n + 1) • (⊤ : Submodule A A)) (AdicCompletion.eval I A (n + 1) x)
  have hx : AdicCompletion.eval I A (n + 1) (x - AdicCompletion.of I A a) = 0 := by
    rw [map_sub, AdicCompletion.eval_of, Submodule.mkQ_apply, ha, sub_self]
  have hd := eval_derivation_eq_zero I hI d n hx
  have he := eval_derivation_eq_zero I hI e n hx
  rw [map_sub, map_sub, sub_eq_zero] at hd he
  exact hd.trans ((congrArg (AdicCompletion.eval I M n) (h a)).trans he.symm)

/-- The constructed extension is the unique extension of the original derivation. -/
theorem completion_unique (d : Derivation R A M)
    (e : Derivation R (AdicCompletion I A) (AdicCompletion I M))
    (h : ∀ a, e (AdicCompletion.of I A a) = AdicCompletion.of I M (d a)) :
    e = completion d I := by
  apply completion_ext I hI
  intro a
  rw [h, completion_of]

end FLT.Mazur.AdicDerivationFiltration
