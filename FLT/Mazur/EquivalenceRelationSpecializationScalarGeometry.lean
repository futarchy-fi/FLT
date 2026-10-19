/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteSpecializations
public import FLT.Mazur.SchemeInvariantSpecializationScalarImage

/-!
# Original scalar geometry throughout a full invariant specialization image

Every scalar prime in the image of the closure of a complete full invariant
prime has a complete representative over its own scalar residue closure.
The representative retains that closed branch and the original scalar map.
This includes points outside any previously chosen principal neighborhood.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (B : (source p q I o).Opens)
  (hB : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ B = B)
  [IsAffine B.toScheme]
local notation "ρ" => restrictedAction (action e I o) B hB
local notation "C" => invariantCoordinates ρ
local notation "K" Q => scalarResidueClosure Q
local notation "u" w => sourceCharacterMap (X := B.toScheme) w ≫ B.ι
attribute [local irreducible] source action restrictedAction Complete
  scalarResidueClosureField scalarResidueClosureAlgebra

variable {R : Type} [CommRing R]
  (σ : R →+* invariantCoordinates (restrictedAction (action e I o) B hB))
local notation "s" => invariantScalarCoordinates ρ σ

/-- Construct complete geometry at every scalar prime in the prescribed closure image. -/
theorem exists_complete_specialization_scalar_character (hs : (s).FiniteType)
    (x : B.toScheme) (hx : B.ι x ∈ completePointLocus (p := p) (q := q) I o)
    (P : PrimeSpectrum R)
    (hP : ∃ Q : PrimeSpectrum C,
      (quotientMap ρ x).asIdeal ≤ Q.asIdeal ∧ PrimeSpectrum.comap σ Q = P) :
    ∃ w : Γ(B.toScheme, ⊤) →+* K P,
      w.comp s = algebraMap R (K P) ∧ Complete I o (u w) ∧
      (quotientMap ρ x).asIdeal ≤ (quotientMap ρ (sourceCharacterMap w default)).asIdeal ∧
      sourceCharacterMap w ≫ scalarMorphism s =
        Spec.map (CommRingCat.ofHom (algebraMap R (K P))) := by
  obtain ⟨w, hw, hQ⟩ := exists_scalar_character_of_invariant_specialization ρ σ hs
    (quotientMap ρ x) P hP
  have hc := complete_orbit_specialization e I o B hB x hx
    (quotientMap ρ (sourceCharacterMap w default)) hQ
  have hm : sourceCharacterMap w default ∈ B.ι ⁻¹' completePointLocus I o := by
    rw [← completeAffineOrbitImage_preimage e I o B hB]
    exact hc
  refine ⟨w, hw, (complete_iff_mem_completePointLocus I o (u w)).mpr hm, hQ, ?_⟩
  rw [sourceCharacterMap_scalar, hw]

end FLT.Mazur.EquivalenceRelationNormalizedFrames
