/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NoetherianClosedImageGenerizations
public import FLT.Mazur.SchemeScalarPrincipalNeighborhood
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Finite original-prime tests for all bad-image accumulation

The generic points of the closed bad locus give a finite test valid at every
original scalar prime. The source need not be affine, and neither a closed
scalar map nor integrality of a bad quotient is required.
-/

@[expose] public noncomputable section
open AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X : Scheme} [NoetherianSpace X]
  (s : R →+* Γ(X, ⊤)) (O : X.Opens)

/-- The safe locus tests whole fibers at all generizations of the original prime. -/
theorem mem_scalarNeighborhoodLocus_iff_generizations (P : PrimeSpectrum R) :
    P ∈ scalarNeighborhoodLocus s O ↔
      ∀ x : X, (scalarMorphism s x).asIdeal ≤ P.asIdeal → x ∈ O := by
  change P ∉ closure (scalarMorphism s '' (O : Set X)ᶜ) ↔ _
  rw [NoetherianClosedImage.mem_closure_image_iff
    (fun x : X ↦ (scalarMorphism s x : PrimeSpectrum R))
    (scalarMorphism s).continuous O.isOpen.isClosed_compl]
  constructor
  · intro h x hx
    by_contra hn
    exact h ⟨x, hn, (PrimeSpectrum.le_iff_specializes _ _).mp hx⟩
  · rintro h ⟨x, hx, hp⟩
    exact hx (h x ((PrimeSpectrum.le_iff_specializes _ _).mpr hp))

/-- Finitely many actual bad points detect every original prime, including accumulation. -/
theorem exists_finite_scalar_bad_primes :
    ∃ F : Set X, F.Finite ∧ F ⊆ (O : Set X)ᶜ ∧
      ∀ P : PrimeSpectrum R, P ∈ scalarNeighborhoodLocus s O ↔
        ∀ x ∈ F, ¬ (scalarMorphism s x).asIdeal ≤ P.asIdeal := by
  obtain ⟨F, hF, hFO, htest⟩ := NoetherianClosedImage.exists_finite_image_generizations
    (fun x : X ↦ (scalarMorphism s x : PrimeSpectrum R))
    (scalarMorphism s).continuous O.isOpen.isClosed_compl
  refine ⟨F, hF, hFO, fun P ↦ ?_⟩
  change P ∉ closure (scalarMorphism s '' (O : Set X)ᶜ) ↔ _
  rw [htest P]
  constructor
  · intro h x hx hp
    exact h ⟨x, hx, (PrimeSpectrum.le_iff_specializes _ _).mp hp⟩
  · rintro h ⟨x, hx, hp⟩
    exact h x hx ((PrimeSpectrum.le_iff_specializes _ _).mpr hp)

/-- Separation from the finite bad primes constructs an original principal denominator. -/
theorem exists_finite_scalar_denominator_tests :
    ∃ F : Set X, F.Finite ∧ F ⊆ (O : Set X)ᶜ ∧
      ∀ P : PrimeSpectrum R,
        (∀ x ∈ F, ¬ (scalarMorphism s x).asIdeal ≤ P.asIdeal) ↔
          ∃ r : R, r ∉ P.asIdeal ∧ X.basicOpen (s r) ≤ O := by
  obtain ⟨F, hF, hFO, htest⟩ := exists_finite_scalar_bad_primes s O
  exact ⟨F, hF, hFO, fun P ↦ (htest P).symm.trans
    (mem_scalarNeighborhoodLocus_iff s O P)⟩

end FLT.Mazur.SchemeScalarPrincipalNeighborhood
