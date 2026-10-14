/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierParameterLocalization
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Inverting a finite Cartier comparison over a target local ring

Localize the whole finite source algebra over the target prime. Regularity
and the original parameter quotient comparison survive this base
localization; the source algebra is not required to be a local ring.
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

include S in
/-- The localized finite algebra is the original target localization when the parameter is local. -/
theorem localized_bijective_of_parameterQuotientMap [IsNoetherianRing R] [Module.Finite R A]
    (t : R) (ht : algebraMap R Rₛ t ∈ Ideal.jacobson (⊥ : Ideal Rₛ))
    (hreg : f t ∈ nonZeroDivisors A)
    (hq : Function.Bijective (parameterQuotientMap (A := A) t)) :
    Function.Bijective (algebraMap Rₛ Aₛ) := by
  let _ : IsNoetherianRing Rₛ := IsLocalization.isNoetherianRing S Rₛ inferInstance
  let _ : Module.Finite Rₛ Aₛ := Module.Finite.of_isLocalization R A S
  apply bijective_of_mod_parameter (algebraMap R Rₛ t) ht
    (localized_parameter_regular S Rₛ Aₛ t hreg)
  · apply localized_mod_parameter_surjective (A := A) S Rₛ Aₛ t
    intro b
    obtain ⟨c, hc⟩ := hq.2 (Ideal.Quotient.mk _ b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨a, (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hc.symm⟩
  · apply localized_mod_parameter_injective (A := A) S Rₛ Aₛ t
    intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hq.1
    rw [parameterQuotientMap_mk, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

/-- At every target prime on the divisor, base localization of the finite map is bijective. -/
theorem atPrime_bijective_of_parameterQuotientMap [IsNoetherianRing R] [Module.Finite R A]
    (p : Ideal R) [p.IsPrime] (t : R) (ht : t ∈ p)
    (hreg : f t ∈ nonZeroDivisors A)
    (hq : Function.Bijective (parameterQuotientMap (A := A) t)) :
    Function.Bijective (algebraMap (Localization.AtPrime p)
      (Localization (Algebra.algebraMapSubmonoid A p.primeCompl))) := by
  apply localized_bijective_of_parameterQuotientMap p.primeCompl _ _ t _ hreg hq
  apply IsLocalRing.maximalIdeal_le_jacobson ⊥
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ p t).mpr ht

end FLT.Mazur.FiniteCartierComparison
