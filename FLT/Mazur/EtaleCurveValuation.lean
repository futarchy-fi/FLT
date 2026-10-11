/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleCurveLocalDomain
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# Valuation local rings of étale curves

The local domain theorem and the unramified maximal-ideal formula imply that
every prime localization is a valuation ring. This includes the generic field,
so proper-extension arguments do not need a separate closed-point case.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.FCurve

/-- Prime localizations of étale algebras over principal domains are valuation rings. -/
theorem valuationRing_atPrime_of_etale_pid
    (A B : Type*) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (q : Ideal B) [q.IsPrime] :
    let _ := isDomain_atPrime_of_etale_pid A B q
    ValuationRing (Localization.AtPrime q) := by
  let _ := isDomain_atPrime_of_etale_pid A B q
  let p := q.under A
  let _ : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  let _ := Localization.AtPrime.algebraOfLiesOver p q
  let _ : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) :=
    .of_comp A _ _
  let _ : Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) :=
    .of_restrictScalars A _ _
  apply ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
    (Localization.AtPrime q)).out 5 2).mp
  rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := Localization.AtPrime p)]
  infer_instance

end FLT.Mazur.FCurve
