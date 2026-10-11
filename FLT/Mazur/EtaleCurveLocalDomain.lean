/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtalePrimeParameterIdeals
public import FLT.Mazur.RegularParameterDomain
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.RingHom.Etale

/-!
# Local domains in étale curves over a principal domain

At a nonzero coordinate prime, flatness transports its regular parameter.
Over the zero prime, the unramified local algebra is a field. Thus every
prime localization is a domain, without assuming the entire chart is connected.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.FCurve

/-- Every local ring of an étale algebra over a principal domain is a domain. -/
theorem isDomain_atPrime_of_etale_pid
    (A B : Type*) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (q : Ideal B) [q.IsPrime] : IsDomain (Localization.AtPrime q) := by
  let p := q.under A
  let _ : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  let _ := Localization.AtPrime.algebraOfLiesOver p q
  let _ : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) :=
    .of_comp A _ _
  let _ : Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) :=
    .of_restrictScalars A _ _
  by_cases hp : p = ⊥
  · have hf : IsField (Localization.AtPrime q) := by
      apply isField_iff_maximalIdeal_eq.mpr
      rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := Localization.AtPrime p),
        ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map]
      exact (congrArg (Ideal.map _) hp).trans (Ideal.map_bot)
    let _ := hf.toField
    infer_instance
  · obtain ⟨t, hr, ht⟩ := regular_parameter_at_prime p hp
    obtain ⟨hs, hm⟩ := regular_parameter_of_flat_unramified
      (B := Localization.AtPrime q) t hr ht
    exact isDomain_of_regular_parameter _ hs hm

end FLT.Mazur.FCurve
