/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RegularParameterIdeals
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Finite colength ideals in local étale coordinates

A flat, essentially finite type, formally unramified local map transports a
regular parameter of the source to a regular parameter of the target.
Finite colength ideals therefore have regular equations. In particular this
applies when the source is a local principal ideal domain that is not a field.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.FCurve

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
  [Algebra.EssFiniteType A B] [Algebra.FormallyUnramified A B] [Module.Flat A B]

/-- A regular parameter remains regular and generates the target maximal ideal. -/
theorem regular_parameter_of_flat_unramified (t : A) (hr : IsRegular t)
    (ht : maximalIdeal A = Ideal.span {t}) :
    IsRegular (algebraMap A B t) ∧
      maximalIdeal B = Ideal.span {algebraMap A B t} := by
  constructor
  · have h := Module.Flat.isSMulRegular_of_isRegular (M := B) hr
    apply (Commute.isRegular_iff (Commute.all _)).mpr
    simpa only [IsSMulRegular, IsLeftRegular, Algebra.smul_def] using h
  · rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := A), ht,
      Ideal.map_span, Set.image_singleton]

/-- Finite colength ideals in a local étale parameter chart have regular generators. -/
theorem regular_generator_of_flat_unramified_parameter (t : A) (hr : IsRegular t)
    (ht : maximalIdeal A = Ideal.span {t}) (I : Ideal B) [IsArtinianRing (B ⧸ I)] :
    ∃ b : B, IsRegular b ∧ I = Ideal.span {b} := by
  obtain ⟨htR, htM⟩ := regular_parameter_of_flat_unramified (B := B) t hr ht
  exact regular_generator_of_artinian_quotient _ htR htM I

/-- A nonfield local principal domain supplies the source parameter without an extra witness. -/
theorem regular_generator_of_flat_unramified_local_pid
    [IsDomain A] [IsPrincipalIdealRing A] (hA : ¬ IsField A)
    (I : Ideal B) [IsArtinianRing (B ⧸ I)] :
    ∃ b : B, IsRegular b ∧ I = Ideal.span {b} := by
  let t := Submodule.IsPrincipal.generator (maximalIdeal A)
  have ht : maximalIdeal A = Ideal.span {t} := (Ideal.span_singleton_generator _).symm
  have ht0 : t ≠ 0 := by
    intro h
    have hm : maximalIdeal A = ⊥ := by simpa [h] using ht
    exact hA (isField_iff_maximalIdeal_eq.mpr hm)
  exact regular_generator_of_flat_unramified_parameter t (IsRegular.of_ne_zero ht0) ht I

end FLT.Mazur.FCurve
