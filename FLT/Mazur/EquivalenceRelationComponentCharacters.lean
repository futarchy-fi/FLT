/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteComponents
public import FLT.Mazur.SchemeInvariantClosedScalarImage

/-!
# Exact full and scalar characters on complete quotient components

Full characters keep their specified field and determine unique original
arrows. Scalar characters instead keep the original scalar residue closure and
the selected closed component; their full invariant center is allowed to move.
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
local notation "u" w => sourceCharacterMap (X := B.toScheme) w ≫ B.ι
attribute [local irreducible] source action restrictedAction Complete
  scalarResidueClosureField scalarResidueClosureAlgebra

/-- Every full character on an anchored preirreducible subset has complete original arrows. -/
theorem exists_complete_component_character
    (Z : Set (quotient ρ)) (hZ : IsPreirreducible Z) (x : B.toScheme)
    (hx : B.ι x ∈ completeInterior (p := p) (q := q) I o)
    (hxZ : quotientMap ρ x ∈ Z)
    {F : Type} [Field F] [IsAlgClosed F] (χ : C →+* F)
    (hχ : PrimeSpectrum.comap χ ⊥ ∈ Z) :
    ∃ w : Γ(B.toScheme, ⊤) →+* F,
      (∀ r : C, w r.val = χ r) ∧ Complete I o (u w) ∧
      ∀ v : Γ(B.toScheme, ⊤) →+* F,
        (∀ r : C, v r.val = χ r) → Complete I o (u v) ∧
        ∃! a : Spec (.of F) ⟶ D,
          a ≫ p = (u w) ≫ first p q I o ∧ a ≫ q = (u v) ≫ first p q I o := by
  exact exists_complete_closed_character e I o B hB χ
    (complete_orbit_preirreducible_subset e I o B hB Z hZ x hx hxZ hχ)

variable {R : Type} [CommRing R]
  (σ : R →+* invariantCoordinates (restrictedAction (action e I o) B hB))
local notation "s" => invariantScalarCoordinates ρ σ
local notation "K" P => scalarResidueClosure P

/-- A scalar lift stays on its anchored closed component and preserves the original map. -/
theorem exists_complete_component_scalar_character (hs : (s).FiniteType)
    (Z : Set (quotient ρ)) (hZ : IsPreirreducible Z) (hclosed : IsClosed Z)
    (x : B.toScheme) (hx : B.ι x ∈ completeInterior (p := p) (q := q) I o)
    (hxZ : quotientMap ρ x ∈ Z) (P : PrimeSpectrum R)
    (hP : P ∈ PrimeSpectrum.comap σ '' Z) :
    ∃ w : Γ(B.toScheme, ⊤) →+* K P,
      w.comp s = algebraMap R (K P) ∧ Complete I o (u w) ∧
      quotientMap ρ (sourceCharacterMap w default) ∈ Z ∧
      sourceCharacterMap w ≫ scalarMorphism s =
        Spec.map (CommRingCat.ofHom (algebraMap R (K P))) := by
  let T : Set B.toScheme := quotientMap ρ ⁻¹' Z
  have hT : IsClosed T := hclosed.preimage (quotientMap ρ).continuous
  have hstable : ∀ (g : Equiv.Perm I) (y : B.toScheme), y ∈ T → (ρ g).hom y ∈ T := by
    intro g y hy
    change quotientMap ρ ((ρ g).hom y) ∈ Z
    rw [← Scheme.Hom.comp_apply, quotientMap_invariant]
    exact hy
  have hp : P ∈ PrimeSpectrum.comap σ '' (closedOrbitImage ρ T hT : Set (quotient ρ)) := by
    obtain ⟨Q, hQ, he⟩ := hP
    obtain ⟨y, hy⟩ := (quotientMap ρ).surjective Q
    refine ⟨Q, ⟨y, ?_, hy⟩, he⟩
    change quotientMap ρ y ∈ Z
    rwa [hy]
  obtain ⟨w, hw, hz⟩ := exists_scalar_character_of_closedOrbit ρ T hT hstable σ hs P hp
  have hc := complete_orbit_preirreducible_subset e I o B hB Z hZ x hx hxZ hz
  have hm : sourceCharacterMap w default ∈ B.ι ⁻¹' completePointLocus I o := by
    rw [← completeAffineOrbitImage_preimage e I o B hB]
    exact hc
  refine ⟨w, hw, (complete_iff_mem_completePointLocus I o (u w)).mpr hm, hz, ?_⟩
  rw [sourceCharacterMap_scalar, hw]

end FLT.Mazur.EquivalenceRelationNormalizedFrames
