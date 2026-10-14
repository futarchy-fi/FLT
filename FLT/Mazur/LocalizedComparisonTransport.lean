/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Localization.Algebra

/-!
# Transporting the original localized ring comparison

A bijective canonical base-localized algebra map remains bijective in any
localization models whose comparison commutes with the original ring map.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteCartierComparison

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Canonical base-localized bijectivity transfers to any commuting localization square. -/
theorem localized_bijective_of_commuting_square (S : Submonoid R)
    (Rₛ Aₛ : Type*) [CommRing Rₛ] [CommRing Aₛ]
    [Algebra R Rₛ] [IsLocalization S Rₛ] [Algebra A Aₛ]
    [IsLocalization (Algebra.algebraMapSubmonoid A S) Aₛ]
    (g : Rₛ →+* Aₛ)
    (hcomm : g.comp (algebraMap R Rₛ) =
      (algebraMap A Aₛ).comp (algebraMap R A))
    (hb : Function.Bijective (algebraMap (Localization S)
      (Localization (Algebra.algebraMapSubmonoid A S)))) : Function.Bijective g := by
  let R₀ := Localization S
  let A₀ := Localization (Algebra.algebraMapSubmonoid A S)
  let eR := IsLocalization.algEquiv S R₀ Rₛ
  let eA := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid A S) A₀ Aₛ
  have he : g.comp eR.toRingHom = eA.toRingHom.comp (algebraMap R₀ A₀) := by
    apply IsLocalization.ringHom_ext S
    ext x
    change g (eR (algebraMap R R₀ x)) = eA (algebraMap R₀ A₀ (algebraMap R R₀ x))
    rw [eR.commutes, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R A A₀, eA.commutes]
    exact DFunLike.congr_fun hcomm x
  have hcomp : Function.Bijective (g ∘ eR) := by
    change Function.Bijective (g.comp eR.toRingHom)
    rw [he]
    exact eA.bijective.comp hb
  exact ⟨fun x y hxy => by
    obtain ⟨x, rfl⟩ := eR.surjective x
    obtain ⟨y, rfl⟩ := eR.surjective y
    exact congrArg eR (hcomp.1 hxy), fun y => by
      obtain ⟨x, hx⟩ := hcomp.2 y
      exact ⟨eR x, hx⟩⟩

end FLT.Mazur.FiniteCartierComparison
