/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteSpecializations
public import FLT.Mazur.EquivalenceRelationCompleteInvariantPrincipal
public import Mathlib.Topology.Irreducible

/-!
# Whole irreducible fixed charts from one complete interior point

The complete orbit locus is closed and a complete interior point supplies a
nonempty invariant principal open. If the full quotient is preirreducible,
this forces completeness everywhere, even when the source chart is reducible.
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

variable [PreirreducibleSpace (quotient (restrictedAction (action e I o) B hB))]

include e hB in
/-- An irreducible full quotient and one complete interior point cover the entire fixed chart. -/
theorem complete_fixed_irreducible_chart (x : B.toScheme)
    (hx : B.ι x ∈ completeInterior (p := p) (q := q) I o) :
    ∀ y : B.toScheme, B.ι y ∈ completePointLocus (p := p) (q := q) I o := by
  obtain ⟨t, ht, hC⟩ := exists_complete_invariant_principal e I o B hB x hx
  let O : (quotient ρ).Opens := PrimeSpectrum.basicOpen t
  have hn : (O : Set (quotient ρ)).Nonempty := by
    refine ⟨quotientMap ρ x, ?_⟩
    change x ∈ quotientMap ρ ⁻¹ᵁ PrimeSpectrum.basicOpen t
    rwa [quotientMap_preimage_basicOpen]
  have hd := O.isOpen.dense hn
  have hs : (O : Set (quotient ρ)) ⊆
      (completeAffineOrbitImage e I o B hB : Set (quotient ρ)) := by
    intro Q hQ
    obtain ⟨y, rfl⟩ := (quotientMap ρ).surjective Q
    have hy : y ∈ B.toScheme.basicOpen t.val := by
      rw [← quotientMap_preimage_basicOpen]
      exact hQ
    exact ⟨y, completeInterior_subset I o (hC y hy), rfl⟩
  have hc := closure_minimal hs (completeAffineOrbitImage e I o B hB).isClosed
  rw [hd.closure_eq] at hc
  intro y
  have hm := hc (Set.mem_univ (quotientMap ρ y))
  change y ∈ B.ι ⁻¹' completePointLocus I o
  rw [← completeAffineOrbitImage_preimage e I o B hB]
  exact hm

/-- Every full invariant character on this entire fixed chart has a complete original orbit. -/
theorem exists_complete_irreducible_character (x : B.toScheme)
    (hx : B.ι x ∈ completeInterior (p := p) (q := q) I o)
    {F : Type} [Field F] [IsAlgClosed F] (χ : C →+* F) :
    ∃ w : Γ(B.toScheme, ⊤) →+* F,
      (∀ r : C, w r.val = χ r) ∧ Complete I o (u w) ∧
      ∀ v : Γ(B.toScheme, ⊤) →+* F,
        (∀ r : C, v r.val = χ r) → Complete I o (u v) ∧
        ∃! a : Spec (.of F) ⟶ D,
          a ≫ p = (u w) ≫ first p q I o ∧ a ≫ q = (u v) ≫ first p q I o := by
  apply exists_complete_closed_character e I o B hB χ
  obtain ⟨y, hy⟩ := (quotientMap ρ).surjective (PrimeSpectrum.comap χ ⊥)
  exact ⟨y, complete_fixed_irreducible_chart e I o B hB x hx y, hy⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames
