/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarPrincipalNeighborhood
public import FLT.Mazur.SchemeMinimalPrimeFiniteTargetOpen

/-!
# Minimal endpoints above prescribed minimal scalar primes

An injective original scalar map lifts each minimal scalar prime to a minimal
prime of the full affine source. No reduction, component replacement or change
of scalar ring occurs. A separated quasi-finite morphism then has a finite
whole-source neighborhood at this endpoint.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarPrincipalNeighborhood
open SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X : Scheme} [IsAffine X]
  (s : R →+* Γ(X, ⊤))

/-- A minimal prime of the original scalar ring has a minimal original affine endpoint. -/
theorem exists_minimal_endpoint_of_injective (hs : Function.Injective s)
    (P : PrimeSpectrum R) (hP : P.asIdeal ∈ minimalPrimes R) :
    ∃ x : X, scalarMorphism s x = P ∧
      (X.isoSpec.hom x).asIdeal ∈ minimalPrimes Γ(X, ⊤) := by
  obtain ⟨Q, hQ, he⟩ := Ideal.exists_minimalPrimes_comap_eq (I := ⊥) s P.asIdeal
    (by rwa [Ideal.comap_bot_of_injective s hs])
  let q : PrimeSpectrum Γ(X, ⊤) := ⟨Q, hQ.1.1⟩
  refine ⟨X.isoSpec.inv q, ?_, ?_⟩
  · change PrimeSpectrum.comap s (X.isoSpec.hom (X.isoSpec.inv q)) = P
    rw [← Scheme.Hom.comp_apply, X.isoSpec.inv_hom_id]
    exact PrimeSpectrum.ext he
  · rw [← Scheme.Hom.comp_apply, X.isoSpec.inv_hom_id]
    exact hQ

variable [IsLocallyNoetherian X] {Y : Scheme} (g : Y ⟶ X)
  [LocallyOfFinitePresentation g] [LocallyQuasiFinite g] [IsSeparated g] [QuasiCompact g]

/-- Every minimal original scalar prime is reached inside the full finite target locus. -/
theorem exists_finite_endpoint_of_injective (hs : Function.Injective s)
    (P : PrimeSpectrum R) (hP : P.asIdeal ∈ minimalPrimes R) :
    ∃ x : X, scalarMorphism s x = P ∧ x ∈ finiteTargetOpen g := by
  obtain ⟨x, hx, hm⟩ := exists_minimal_endpoint_of_injective s hs P hP
  exact ⟨x, hx, affine_minimalPrime_mem_finiteTarget g x hm⟩

end FLT.Mazur.SchemeScalarPrincipalNeighborhood
