/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteKernelCorrectionOperator
public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Clearing denominators in the full finite kernel correction operator

A localized correction gives an actual original coefficient tuple and one
original denominator. No finite generation over the scalar ring is needed:
the entire tuple is localized as a module, retaining both endpoint actions.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteKernelCorrections
variable {R : Type*} [CommRing R] (U : Submonoid R)
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (F : M →ₗ[R] N)

/-- The original module's localization map, with its denominator visible. -/
def localizedMap : LocalizedModule U M →ₗ[R] LocalizedModule U N :=
  IsLocalizedModule.map U (LocalizedModule.mkLinearMap U M)
    (LocalizedModule.mkLinearMap U N) F

/-- Evaluation of the localized map does not change denominators. -/
theorem localizedMap_mk (x : M) (s : U) :
    localizedMap U F (LocalizedModule.mk x s) = LocalizedModule.mk (F x) s :=
  IsLocalizedModule.map_LocalizedModules U F x s

/-- Local image membership clears to one original denominator and one original preimage. -/
theorem localized_mem_range_iff (x : N) :
    LocalizedModule.mk x (1 : U) ∈ LinearMap.range (localizedMap U F) ↔
      ∃ s : U, ∃ y : M, F y = s.val • x := by
  constructor
  · rintro ⟨v, hv⟩
    induction v using LocalizedModule.induction_on with
    | _ y s =>
      rw [localizedMap_mk, LocalizedModule.mk_eq] at hv
      obtain ⟨a, ha⟩ := hv
      refine ⟨a * s, a.val • y, ?_⟩
      simpa only [map_smul, Submonoid.coe_mul, mul_smul, one_smul,
        Submonoid.smul_def] using ha
  · rintro ⟨s, y, hy⟩
    refine ⟨LocalizedModule.mk y s, ?_⟩
    rw [localizedMap_mk, LocalizedModule.mk_eq]
    exact ⟨1, by simpa only [one_smul, Submonoid.smul_def] using hy⟩

/-- A localized additive correction is exactly an original correction after one multiplier. -/
theorem localized_correction_iff (x : N) :
    (∃ v, LocalizedModule.mk x (1 : U) + localizedMap U F v = 0) ↔
      ∃ s : U, ∃ y : M, s.val • x + F y = 0 := by
  have h : (∃ v, LocalizedModule.mk x (1 : U) + localizedMap U F v = 0) ↔
      LocalizedModule.mk (-x) (1 : U) ∈ LinearMap.range (localizedMap U F) := by
    simp only [LinearMap.mem_range, LocalizedModule.mk_neg]
    apply exists_congr
    intro v
    rw [add_comm, add_eq_zero_iff_eq_neg]
  rw [h, localized_mem_range_iff]
  simp only [smul_neg]
  apply exists_congr
  intro s
  apply exists_congr
  intro y
  rw [add_comm, add_eq_zero_iff_eq_neg]

variable {Q C : Type*} [CommRing Q] [CommRing C] [Algebra R Q] [Algebra R C]
  {n : ℕ} (z : Fin n → Q) (p q : Q →ₐ[R] C)

/-- A localized finite-coordinate solution produces actual ambient coefficients. -/
theorem localized_operator_correction_iff (x : C) :
    (∃ v, LocalizedModule.mk x (1 : U) + localizedMap U (operator R z p q) v = 0) ↔
      ∃ s : U, ∃ u : Fin n → Q,
        s.val • x + ∑ j, (p (u j) * p (z j) - q (u j) * q (z j)) = 0 := by
  rw [localized_correction_iff]
  simp only [operator_apply]

end FLT.Mazur.FiniteKernelCorrections
