/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicDerivationUniqueness

/-!
# Derivations into separated modules over a completion

The uniqueness argument only needs separation of the target for the
original ideal filtration. This allows transport of cotangent comparisons
between different original algebras with isomorphic formal completions.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicSeparatedDerivation

variable {R A N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) [AddCommGroup N] [Module R N] [Module A N]
  [Module (AdicCompletion I A) N] [IsScalarTower A (AdicCompletion I A) N]
  (hI : I.FG)

include hI

/-- A derivation into any completed-ring module loses at most one original ideal power. -/
theorem map_mem_pow
    (d : Derivation R (AdicCompletion I A) N) (n : ℕ)
    {x : AdicCompletion I A} (hx : AdicCompletion.eval I A (n + 1) x = 0) :
    d x ∈ I ^ n • (⊤ : Submodule A N) := by
  have hx' : x ∈ (I.map (algebraMap A (AdicCompletion I A))) ^ (n + 1) := by
    rw [← Ideal.map_pow]
    change x ∈ ((I ^ (n + 1)).map (algebraMap A (AdicCompletion I A))).restrictScalars A
    rw [← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval hI]
    exact hx
  have hd := AdicDerivationFiltration.map_mem_pow_smul d
    (I.map (algebraMap A (AdicCompletion I A))) n hx'
  rw [← Ideal.map_pow] at hd
  change d x ∈ (((I ^ n).map (algebraMap A (AdicCompletion I A))) •
    (⊤ : Submodule (AdicCompletion I A) N)).restrictScalars A at hd
  rwa [Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top] at hd

/-- Values on original sections determine derivations into an ideal-adically separated target. -/
theorem ext_of [IsHausdorff I N] (d e : Derivation R (AdicCompletion I A) N)
    (h : ∀ a, d (AdicCompletion.of I A a) = e (AdicCompletion.of I A a)) : d = e := by
  ext x : 1
  apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
  intro n
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective
    (I ^ (n + 1) • (⊤ : Submodule A A)) (AdicCompletion.eval I A (n + 1) x)
  have hx : AdicCompletion.eval I A (n + 1) (x - AdicCompletion.of I A a) = 0 := by
    rw [map_sub, AdicCompletion.eval_of, Submodule.mkQ_apply, ha, sub_self]
  have hd := map_mem_pow I hI d n hx
  have he := map_mem_pow I hI e n hx
  rw [map_sub] at hd he
  rw [SModEq.sub_mem]
  convert (I ^ n • (⊤ : Submodule A N)).sub_mem hd he using 1
  rw [h]
  abel

end FLT.Mazur.AdicSeparatedDerivation
