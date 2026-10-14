/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCartierLocalizedComparison
public import FLT.Mazur.HilbertLocalizationIsomorphismOpen

/-!
# Spreading the original finite Cartier comparison

The inverse over a target prime spreads to a principal neighborhood using
finite presentation. All comparisons are localizations of the original
algebra map, rather than newly chosen maps between the underlying modules.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteCartierComparison

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The ring-localized comparison and module-localized comparison have the same bijectivity. -/
theorem localized_algebraMap_bijective_iff (S : Submonoid R) :
    Function.Bijective (algebraMap (Localization S)
      (Localization (Algebra.algebraMapSubmonoid A S))) ↔
      Function.Bijective (LocalizedModule.map S (Algebra.linearMap R A)) := by
  let Rₛ := Localization S
  let Aₛ := Localization (Algebra.algebraMapSubmonoid A S)
  have he : IsLocalization.mapₐ S Rₛ Rₛ Aₛ (Algebra.ofId R A) = Algebra.ofId Rₛ Aₛ := by
    exact Subsingleton.elim _ _
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
    (Algebra.linearMap R Rₛ) (IsScalarTower.toAlgHom R A Aₛ).toLinearMap]
  rw [IsLocalization.map_linearMap_eq_toLinearMap_mapₐ S Rₛ Aₛ, he]
  rfl

/-- A prime on the Cartier divisor has a principal neighborhood with invertible comparison. -/
theorem exists_notMem_bijective_of_parameterQuotientMap
    [IsNoetherianRing R] [Module.Finite R A] (p : Ideal R) [p.IsPrime]
    (t : R) (ht : t ∈ p) (hreg : algebraMap R A t ∈ nonZeroDivisors A)
    (hq : Function.Bijective (parameterQuotientMap (A := A) t)) :
    ∃ r : R, r ∉ p ∧ Function.Bijective (algebraMap (Localization.Away r)
      (Localization (Algebra.algebraMapSubmonoid A (.powers r)))) := by
  let _ : Module.FinitePresentation R A := Module.finitePresentation_of_finite R A
  have hp := atPrime_bijective_of_parameterQuotientMap p t ht hreg hq
  have hl := (localized_algebraMap_bijective_iff (A := A) p.primeCompl).mp hp
  obtain ⟨r, hr, hb⟩ := Module.FinitePresentation.exists_notMem_bijective
    (Algebra.linearMap R A) p (LocalizedModule.mkLinearMap p.primeCompl R)
    (LocalizedModule.mkLinearMap p.primeCompl A) hl
  exact ⟨r, hr, (localized_algebraMap_bijective_iff (A := A) (.powers r)).mpr hb⟩

end FLT.Mazur.FiniteCartierComparison
