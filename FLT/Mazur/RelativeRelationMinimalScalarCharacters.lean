/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationMinimalScalarEndpoints
public import FLT.Mazur.ScalarResidueClosureGeometry
public import FLT.Mazur.EquivalenceRelationFiniteCompleteInterior

/-!
# Complete geometric frames over prescribed minimal scalar primes

Every minimal prime of the original invariant section ring has a complete
interior frame over its own canonical residue closure. Finite type of the
original source coordinates supplies the exact scalar character; no extension
of that geometric field or replacement of the scalar domain is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.RelativeRelationOrbit
open SchemeScalarPrincipalNeighborhood SchemeFiniteGroupQuotient SchemeOpenEnvelope
open EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q)
  (W : TopologicalSpace.Opens (Orbit e))
set_option quotPrecheck false
local notation "E" => (pullOpen e W).val
local notation "Ω" => (invariantSheaf e).obj.obj (op W)
local notation "s" => orbitScalarCoordinates e W

/-- Integer finite type of original coordinates implies finite type over the full scalar ring. -/
theorem orbitScalarCoordinates_finiteType [Algebra.FiniteType ℤ Γ((E).toScheme, ⊤)] :
    (s).FiniteType := by
  apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℤ Ω)
  have he : (s).comp (algebraMap ℤ Ω) = algebraMap ℤ Γ((E).toScheme, ⊤) :=
    Subsingleton.elim _ _
  rw [he]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

attribute [local irreducible] invariantSheaf orbitScalarCoordinates
  scalarResidueClosureField scalarResidueClosureAlgebra
  EquivalenceRelationNormalizedFrames.source first completeInterior Complete
  scalarMorphism finiteTargetOpen

variable [IsLocallyNoetherian A.left] [Etale p.left] [IsSeparated p.left]
  [QuasiCompact p.left]
local notation "K" P => scalarResidueClosure P

/-- Construct a full-character geometric endpoint in the original finite relation locus. -/
theorem exists_minimal_scalar_geometric_endpoint (P : PrimeSpectrum Ω) (hW : IsAffineOpen E)
    (hs : (s).FiniteType) (hP : P.asIdeal ∈ minimalPrimes Ω) :
    ∃ b : Spec (.of (K P)) ⟶ (E).toScheme,
      b ≫ scalarMorphism s = Spec.map (CommRingCat.ofHom (algebraMap Ω (K P))) ∧
      (b ≫ (E).ι) (⊥ : PrimeSpectrum (K P)) ∈ finiteTargetOpen p.left := by
  let _ : IsAffine (E).toScheme := hW
  let _ := QuasiCompactEtaleGeometricSections.locallyQuasiFinite p.left
  obtain ⟨w, hw, hf⟩ := exists_minimal_scalar_sealed_character s P (p.left ∣_ E)
    hs (orbitScalarCoordinates_injective e W) hP
  refine ⟨sourceCharacterMap w, ?_, ?_⟩
  · exact (sourceCharacterMap_scalar s w).trans
      (congrArg (fun t : Ω →+* (K P) ↦ Spec.map (CommRingCat.ofHom t)) hw)
  · rwa [finiteTargetOpen_restrict] at hf

/-- Complete interior frames exist over the SAME original minimal scalar residue closure. -/
theorem exists_minimal_scalar_complete_frame (P : PrimeSpectrum Ω)
    (er : CategoryTheory.EquivalenceRelation p.left q.left) (hW : IsAffineOpen E)
    (hs : (s).FiniteType) (hP : P.asIdeal ∈ minimalPrimes Ω) :
    ∃ (b : Spec (.of (K P)) ⟶ (E).toScheme) (n : ℕ) (o : Fin n)
      (u : Spec (.of (K P)) ⟶ source p.left q.left (Fin n) o),
      b ≫ scalarMorphism s = Spec.map (CommRingCat.ofHom (algebraMap Ω (K P))) ∧
      u ≫ first p.left q.left (Fin n) o = b ≫ (E).ι ∧
      Complete (Fin n) o u ∧
      u (⊥ : PrimeSpectrum (K P)) ∈ completeInterior (p := p.left) (q := q.left) (Fin n) o := by
  obtain ⟨b, hb, hf⟩ := exists_minimal_scalar_geometric_endpoint e W P hW hs hP
  obtain ⟨n, o, u, hu, hc⟩ := exists_complete_normalized_lift er (b ≫ (E).ι)
  refine ⟨b, n, o, u, hb, hu, hc, complete_mem_interior_of_finiteTarget _ _ _
    ((complete_iff_mem_completePointLocus _ _ u).mp hc) ?_⟩
  change (u ≫ first p.left q.left (Fin n) o) (⊥ : PrimeSpectrum (K P)) ∈ _
  rwa [hu]

end FLT.Mazur.RelativeRelationOrbit
