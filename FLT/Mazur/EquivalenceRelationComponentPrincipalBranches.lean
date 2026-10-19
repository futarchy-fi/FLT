/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationComponentCharacters
public import FLT.Mazur.ScalarClosedPrincipalBranches

/-!
# Constructed principal scalar branches with complete frame geometry

The selected closed quotient component supplies equations in the unchanged
source coordinate ring. Chevalley constructs a principal neighborhood along
each minimal prime of their scalar contraction. Every prime on that branch
has a complete lift over its original scalar residue closure, retaining the
chosen component. Finite presentation is required only for this image argument.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeScalarPrincipalNeighborhood
open ScalarClosedImageCoverage
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (B : (source p q I o).Opens)
  (hB : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ B = B)
  [IsAffine B.toScheme]
local notation "ρ" => restrictedAction (action e I o) B hB
local notation "C" => invariantCoordinates ρ
local notation "i" => invariantScalarCoordinates ρ (RingHom.id C)
local notation "u" w => sourceCharacterMap (X := B.toScheme) w ≫ B.ι
attribute [local irreducible] source action restrictedAction Complete
attribute [local semireducible] scalarResidueClosure

variable {R : Type} [CommRing R]
  (σ : R →+* invariantCoordinates (restrictedAction (action e I o) B hB))
local notation "s" => invariantScalarCoordinates ρ σ
local notation "K" P => scalarResidueClosure P

/-- Construct a principal original scalar branch whose complete lifts retain the component. -/
theorem exists_complete_component_principal_branch
    (Z : Set (quotient ρ)) (hZ : IsPreirreducible Z) (hclosed : IsClosed Z)
    (x : B.toScheme) (hx : B.ι x ∈ completeInterior (p := p) (q := q) I o)
    (hxZ : quotientMap ρ x ∈ Z)
    (hfp : ((Ideal.Quotient.mk ((PrimeSpectrum.vanishingIdeal Z).map i)).comp s).FinitePresentation)
    (P : PrimeSpectrum R)
    (hP : P.asIdeal ∈ (((PrimeSpectrum.vanishingIdeal Z).map i).comap s).minimalPrimes) :
    ∃ t : R, t ∉ P.asIdeal ∧ ∀ Q : PrimeSpectrum R,
      P.asIdeal ≤ Q.asIdeal → t ∉ Q.asIdeal →
      ∃ w : Γ(B.toScheme, ⊤) →+* K Q,
        w.comp s = algebraMap R (K Q) ∧ Complete I o (u w) ∧
        quotientMap ρ (sourceCharacterMap w default) ∈ Z ∧
        sourceCharacterMap w ≫ scalarMorphism s =
          Spec.map (CommRingCat.ofHom (algebraMap R (K Q))) := by
  obtain ⟨t, ht, h⟩ := exists_closed_scalar_principal_branch s
    ((PrimeSpectrum.vanishingIdeal Z).map i) hfp P hP
  refine ⟨t, ht, fun Q hPQ htQ ↦ ?_⟩
  obtain ⟨w, hw, hj⟩ := h Q hPQ htQ
  have hz : quotientMap ρ (sourceCharacterMap w default) ∈ Z := by
    rw [← hclosed.closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    change (sourceCharacterMap w ≫ quotientMap ρ) default ∈
      PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal Z : Set C)
    rw [sourceCharacterMap_quotient]
    intro r hr
    exact hj (i r) (Ideal.mem_map_of_mem i hr)
  have hc := complete_orbit_preirreducible_subset e I o B hB Z hZ x hx hxZ hz
  have hm : sourceCharacterMap w default ∈ B.ι ⁻¹' completePointLocus I o := by
    rw [← completeAffineOrbitImage_preimage e I o B hB]
    exact hc
  refine ⟨w, hw, (complete_iff_mem_completePointLocus I o (u w)).mpr hm, hz, ?_⟩
  rw [sourceCharacterMap_scalar, hw]
  rfl

end FLT.Mazur.EquivalenceRelationNormalizedFrames
