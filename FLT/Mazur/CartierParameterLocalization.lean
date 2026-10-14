/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCartierQuotientIso
public import Mathlib.RingTheory.Localization.Algebra

/-!
# Retaining the Cartier comparison under base localization

Both rings are localized at the same base multiplicative set. The source
algebra need not be local. The full parameter ideals, including their
scheme structure, retain surjectivity and injectivity of the comparison.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteCartierComparison

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (S : Submonoid R) (Rₛ Aₛ : Type*) [CommRing Rₛ] [CommRing Aₛ]
variable [Algebra R Rₛ] [IsLocalization S Rₛ]
variable [Algebra A Aₛ] [Algebra R Aₛ] [Algebra Rₛ Aₛ]
variable [IsScalarTower R A Aₛ] [IsScalarTower R Rₛ Aₛ]
variable [IsLocalization (Algebra.algebraMapSubmonoid A S) Aₛ]
local notation "f" => algebraMap R A
local notation "fₛ" => algebraMap Rₛ Aₛ
include S

omit [IsLocalization S Rₛ] in
/-- Base localization retains the original regular pulled parameter. -/
theorem localized_parameter_regular (t : R) (ht : f t ∈ nonZeroDivisors A) :
    fₛ (algebraMap R Rₛ t) ∈ nonZeroDivisors Aₛ := by
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R A Aₛ]
  exact IsLocalization.nonZeroDivisors_le_comap (Algebra.algebraMapSubmonoid A S) Aₛ ht

/-- Injectivity modulo the original parameter survives base localization. -/
theorem localized_mod_parameter_injective (t : R)
    (hi : ∀ a : R, f a ∈ Ideal.span {f t} → a ∈ Ideal.span {t}) :
    ∀ a : Rₛ, fₛ a ∈ Ideal.span {fₛ (algebraMap R Rₛ t)} →
      a ∈ Ideal.span {algebraMap R Rₛ t} := by
  intro a ha
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq S a
  have he : Ideal.span {fₛ (algebraMap R Rₛ t)} =
      (Ideal.span {f t}).map (algebraMap A Aₛ) := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    exact (IsScalarTower.algebraMap_apply R Rₛ Aₛ t).symm.trans
      (IsScalarTower.algebraMap_apply R A Aₛ t)
  rw [he, IsLocalization.algebraMap_mk' A] at ha
  obtain ⟨u, hu, hua⟩ :=
    (IsLocalization.mk'_mem_map_algebraMap_iff _ _ _ _ _).mp ha
  obtain ⟨r, hr, rfl⟩ := hu
  rw [← map_mul] at hua
  rw [← Set.image_singleton, ← Ideal.map_span]
  exact (IsLocalization.mk'_mem_map_algebraMap_iff S Rₛ _ _ _).mpr
    ⟨r, hr, hi (r * a) hua⟩

/-- Every numerator lift modulo the parameter gives a localized lift with the same denominator. -/
theorem localized_mod_parameter_surjective (t : R)
    (hs : ∀ b : A, ∃ a : R, b - f a ∈ Ideal.span {f t}) :
    ∀ b : Aₛ, ∃ a : Rₛ, b - fₛ a ∈ Ideal.span {fₛ (algebraMap R Rₛ t)} := by
  intro b
  obtain ⟨b, u, rfl⟩ :=
    IsLocalization.exists_mk'_eq (Algebra.algebraMapSubmonoid A S) b
  obtain ⟨s, hsS, he⟩ := u.property
  obtain rfl : u = ⟨f s, ⟨s, hsS, rfl⟩⟩ := Subtype.ext he.symm
  obtain ⟨a, ha⟩ := hs b
  refine ⟨IsLocalization.mk' Rₛ a ⟨s, hsS⟩, ?_⟩
  rw [IsLocalization.algebraMap_mk' A]
  have hm : algebraMap A Aₛ (b - f a) ∈
      Ideal.span {fₛ (algebraMap R Rₛ t)} := by
    have := Ideal.mem_map_of_mem (algebraMap A Aₛ) ha
    simpa only [Ideal.map_span, Set.image_singleton,
      ← IsScalarTower.algebraMap_apply] using this
  simpa only [map_sub, sub_mul, ← IsLocalization.mk'_eq_mul_mk'_one] using
    (Ideal.span {fₛ (algebraMap R Rₛ t)}).mul_mem_right
      (IsLocalization.mk' (M := Algebra.algebraMapSubmonoid A S)
        Aₛ 1 ⟨f s, ⟨s, hsS, rfl⟩⟩) hm

end FLT.Mazur.FiniteCartierComparison
