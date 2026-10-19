/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarMinimalCharacterPropagation
public import FLT.Mazur.SchemeOriginalScalarOpenCorrections

/-!
# Descend scalar going down from the original source

A surjective cover of coefficient spectra transfers going down from its
composite scalar map. Applied to finite-group invariants, flatness need only
be proved on the actual original source coordinates. Neither averaging nor
invertibility of the group order is used.
-/

@[expose] public noncomputable section
universe u
namespace FLT.Mazur.ScalarTestLocalization
variable {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
  (s : R →+* B) (i : B →+* C)

/-- Lift a coefficient prime to the cover, go down there, and contract the resulting prime. -/
theorem scalar_generalizing_of_surjective_cover
    (hi : Function.Surjective (PrimeSpectrum.comap i))
    (hs : GeneralizingMap (PrimeSpectrum.comap (i.comp s))) :
    GeneralizingMap (PrimeSpectrum.comap s) := by
  intro q Q hQ
  obtain ⟨r, hr⟩ := hi q
  have h : Q ⤳ PrimeSpectrum.comap (i.comp s) r := by
    change Q ⤳ PrimeSpectrum.comap s (PrimeSpectrum.comap i r)
    rw [hr]
    exact hQ
  obtain ⟨r', hr', he⟩ := hs h
  refine ⟨PrimeSpectrum.comap i r', ?_, he⟩
  rw [← hr]
  exact hr'.map (PrimeSpectrum.continuous_comap i)

/-- Flatness on a spectrum-surjective source suffices for scalar going down downstairs. -/
theorem scalar_generalizing_of_flat_cover
    (hi : Function.Surjective (PrimeSpectrum.comap i)) (hs : (i.comp s).Flat) :
    GeneralizingMap (PrimeSpectrum.comap s) :=
  scalar_generalizing_of_surjective_cover s i hi hs.generalizingMap_comap

end FLT.Mazur.ScalarTestLocalization

open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
open SchemeCoordinateAction ScalarTestLocalization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {G : Type} [Group G] [Finite G]
  {X : Scheme} (ρ : G →* Aut X) (s : R →+* invariantCoordinates ρ)

/-- Flatness of the actual source scalar algebra gives going down on invariant coordinates. -/
theorem invariantScalar_generalizing_of_source_flat
    (hf : (invariantScalarCoordinates ρ s).Flat) :
    GeneralizingMap (PrimeSpectrum.comap s) := by
  let _ := coordinateAction ρ
  apply scalar_generalizing_of_flat_cover s (FiniteGroupQuotient.inclusion G Γ(X, ⊤))
    (FiniteGroupQuotient.spectrum_surjective G Γ(X, ⊤))
  exact hf

/-- Source flatness propagates generic containment through the full scalar localization. -/
theorem invariant_ideal_le_character_of_minimal_source_flat
    (P : PrimeSpectrum R) (J : Ideal (invariantCoordinates ρ)) (hs : s.FiniteType)
    (hf : (invariantScalarCoordinates ρ s).Flat)
    (hJ : ∀ Q : PrimeSpectrum R, Q.asIdeal ∈ minimalPrimes R → Q ≤ P →
      ∀ χ : invariantCoordinates ρ →+* AlgebraicClosure Q.asIdeal.ResidueField,
        χ.comp s = algebraMap R _ → J ≤ RingHom.ker χ)
    (Q : PrimeSpectrum R) (hQP : Q ≤ P)
    (χ : invariantCoordinates ρ →+* AlgebraicClosure Q.asIdeal.ResidueField)
    (hχ : χ.comp s = algebraMap R _) : J ≤ RingHom.ker χ :=
  ideal_le_character_of_minimal_scalar_characters s P J hs
    (invariantScalar_generalizing_of_source_flat ρ s hf) hJ Q hQP χ hχ

end FLT.Mazur.SchemeFiniteGroupQuotient
