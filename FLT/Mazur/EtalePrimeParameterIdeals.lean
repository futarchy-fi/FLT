/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleLocalParameterIdeals
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Regular equations above nonzero primes of a principal domain

A generator of the source prime becomes a regular parameter in its actual
localization. This constructs the parameter required by the local étale
criterion, including for polynomial coordinates over arbitrary fields.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.FCurve

variable {A : Type*} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]

/-- Localization at a nonzero principal prime has a constructed regular parameter. -/
theorem regular_parameter_at_prime (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥) :
    ∃ t : Localization.AtPrime p, IsRegular t ∧
      maximalIdeal (Localization.AtPrime p) = Ideal.span {t} := by
  let a := Submodule.IsPrincipal.generator p
  have ha : p = Ideal.span {a} := (Ideal.span_singleton_generator _).symm
  have ha0 : a ≠ 0 := by
    intro h
    apply hp
    simpa [h] using ha
  refine ⟨algebraMap A (Localization.AtPrime p) a, ?_, ?_⟩
  · have h := Module.Flat.isSMulRegular_of_isRegular (M := Localization.AtPrime p)
      (IsRegular.of_ne_zero ha0)
    apply (Commute.isRegular_iff (Commute.all _)).mpr
    simpa only [IsSMulRegular, IsLeftRegular, Algebra.smul_def] using h
  · rw [← Localization.AtPrime.map_eq_maximalIdeal]
    simpa only [Ideal.map_span, Set.image_singleton] using
      congrArg (Ideal.map (algebraMap A (Localization.AtPrime p))) ha

/-- Finite colength ideals above a nonzero coordinate prime are regular principal. -/
theorem regular_generator_of_localized_pid_coordinate
    (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥)
    (B : Type*) [CommRing B] [IsLocalRing B] [Algebra (Localization.AtPrime p) B]
    [IsLocalHom (algebraMap (Localization.AtPrime p) B)]
    [Algebra.EssFiniteType (Localization.AtPrime p) B]
    [Algebra.FormallyUnramified (Localization.AtPrime p) B]
    [Module.Flat (Localization.AtPrime p) B]
    (I : Ideal B) [IsArtinianRing (B ⧸ I)] :
    ∃ b : B, IsRegular b ∧ I = Ideal.span {b} := by
  obtain ⟨t, ht, hm⟩ := regular_parameter_at_prime p hp
  exact regular_generator_of_flat_unramified_parameter t ht hm I

end FLT.Mazur.FCurve
