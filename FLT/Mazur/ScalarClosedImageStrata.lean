/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarConstructibleStrata
public import FLT.Mazur.ScalarClosedGeometricLifts

/-!
# All scalar image strata of closed source equations

Finite presentation constructs a finite covering of the entire actual image,
including the boundary outside any previously chosen principal open. Each
piece supplies a character over the original prime's own residue closure.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarClosedImageCoverage
open ScalarTestLocalization ScalarConstructibleStrata
variable {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) (J : Ideal S)

/-- Closed-source scalar characters are exactly primes in the quotient source's image. -/
theorem closed_scalar_character_iff_range
    (hft : ((Ideal.Quotient.mk J).comp s).FiniteType) (P : PrimeSpectrum R) :
    (∃ w : S →+* AlgebraicClosure P.asIdeal.ResidueField,
      w.comp s = algebraMap R _ ∧ ∀ b ∈ J, w b = 0) ↔
      P ∈ Set.range (PrimeSpectrum.comap ((Ideal.Quotient.mk J).comp s)) := by
  let π := Ideal.Quotient.mk J
  constructor
  · rintro ⟨w, hw, hj⟩
    let v := Ideal.Quotient.lift J w hj
    refine ⟨PrimeSpectrum.comap v ⊥, ?_⟩
    change PrimeSpectrum.comap (v.comp (π.comp s)) ⊥ = P
    have he : v.comp (π.comp s) = algebraMap R _ := hw
    rw [he, algebraicClosure_residue_center]
  · rintro ⟨q, hq⟩
    obtain ⟨v, hv, _⟩ := exists_residue_geometric_failure (π.comp s) P hft 1 q hq
      q.isPrime.one_notMem
    refine ⟨v.comp π, hv, fun b hb ↦ ?_⟩
    change v (Ideal.Quotient.mk J b) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero]

/-- Construct finitely many exact scalar pieces covering all closed-source characters. -/
theorem exists_closed_scalar_image_strata
    (hfp : ((Ideal.Quotient.mk J).comp s).FinitePresentation) :
    ∃ pieces : Finset (R × Finset R), ∀ P : PrimeSpectrum R,
      (∃ a ∈ pieces, a.1 ∉ P.asIdeal ∧ ∀ r ∈ a.2, r ∈ P.asIdeal) ↔
      ∃ w : S →+* AlgebraicClosure P.asIdeal.ResidueField,
        w.comp s = algebraMap R _ ∧ ∀ b ∈ J, w b = 0 := by
  obtain ⟨pieces, h⟩ := exists_finite_principal_strata _
    (PrimeSpectrum.isConstructible_range_comap hfp)
  refine ⟨pieces, fun P ↦ (h P).symm.trans ?_⟩
  exact (closed_scalar_character_iff_range s J
    (RingHom.FiniteType.of_finitePresentation hfp) P).symm

/-- Finite type over a Noetherian scalar ring supplies the needed quotient presentation. -/
theorem exists_closed_scalar_image_strata_of_finiteType [IsNoetherianRing R]
    (hs : s.FiniteType) :
    ∃ pieces : Finset (R × Finset R), ∀ P : PrimeSpectrum R,
      (∃ a ∈ pieces, a.1 ∉ P.asIdeal ∧ ∀ r ∈ a.2, r ∈ P.asIdeal) ↔
      ∃ w : S →+* AlgebraicClosure P.asIdeal.ResidueField,
        w.comp s = algebraMap R _ ∧ ∀ b ∈ J, w b = 0 := by
  let g := (Ideal.Quotient.mk J).comp s
  have ht : g.FiniteType :=
    (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective).comp hs
  have hp : g.FinitePresentation := by
    let _ := g.toAlgebra
    exact Algebra.FinitePresentation.of_finiteType.mp ht
  exact exists_closed_scalar_image_strata s J hp

end FLT.Mazur.ScalarClosedImageCoverage
