/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarMinimalEndpoint
public import FLT.Mazur.ScalarAlgebraicClosureTests
public import FLT.Mazur.SchemeFiniteGroupGeometricTests

/-!
# Geometric lifts in a prescribed open over the same scalar residue closure

A finite type scalar map turns any original fiber point in an open into a
point over the canonical algebraic closure of the scalar residue field. The
entire scalar character, and not just its prime kernel, is preserved.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarPrincipalNeighborhood
open SchemeFiniteGroupQuotient ScalarTestLocalization SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X : Scheme} [IsAffine X]
  (s : R →+* Γ(X, ⊤)) (P : PrimeSpectrum R)
local notation "K" => AlgebraicClosure P.asIdeal.ResidueField

/-- Realizing a source character preserves its exact original scalar restriction. -/
theorem sourceCharacterMap_scalar {L : Type} [Field L] (w : Γ(X, ⊤) →+* L) :
    sourceCharacterMap w ≫ scalarMorphism s = Spec.map (CommRingCat.ofHom (w.comp s)) := by
  change (Spec.map (CommRingCat.ofHom w) ≫ X.isoSpec.inv) ≫
    X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom s) = _
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  exact (Spec.map_comp _ _).symm

/-- Nonempty original open fibers have points over the unchanged scalar residue closure. -/
theorem exists_scalar_character_in_open (hs : s.FiniteType)
    (O : X.Opens) (x : X) (hx : x ∈ O) (hxP : scalarMorphism s x = P) :
    ∃ w : Γ(X, ⊤) →+* K, w.comp s = algebraMap R K ∧ sourceCharacterMap w default ∈ O := by
  obtain ⟨r, hrO, hxr⟩ := (isAffineOpen_top X).exists_basicOpen_le ⟨x, hx⟩ (by trivial)
  have hr : r ∉ (X.isoSpec.hom x).asIdeal := by
    change X.toSpecΓ x ∈ PrimeSpectrum.basicOpen r
    change x ∈ X.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen r
    rwa [X.toSpecΓ_preimage_basicOpen]
  obtain ⟨w, hw, hwr⟩ := exists_residue_geometric_failure s P hs r (X.isoSpec.hom x) hxP hr
  refine ⟨w, hw, hrO ?_⟩
  rw [← X.toSpecΓ_preimage_basicOpen]
  change (sourceCharacterMap w ≫ X.isoSpec.hom) default ∈ PrimeSpectrum.basicOpen r
  change ((Spec.map (CommRingCat.ofHom w) ≫ X.isoSpec.inv) ≫ X.isoSpec.hom) default ∈ _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact hwr

variable [IsLocallyNoetherian X] {Y : Scheme} (g : Y ⟶ X)
  [LocallyOfFinitePresentation g] [LocallyQuasiFinite g] [IsSeparated g] [QuasiCompact g]

/-- Minimal scalar primes have full scalar-character lifts in the whole finite target locus. -/
theorem exists_minimal_scalar_finite_character (hs : s.FiniteType)
    (hi : Function.Injective s) (hP : P.asIdeal ∈ minimalPrimes R) :
    ∃ w : Γ(X, ⊤) →+* K, w.comp s = algebraMap R K ∧
      sourceCharacterMap w default ∈ finiteTargetOpen g := by
  obtain ⟨x, hx, hf⟩ := exists_finite_endpoint_of_injective s g hi P hP
  exact exists_scalar_character_in_open s P hs (finiteTargetOpen g) x hf hx

end FLT.Mazur.SchemeScalarPrincipalNeighborhood
