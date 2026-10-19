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
# Complete components of reducible fixed frame quotients

A complete interior point on a preirreducible subset of the full quotient
forces that entire subset into the closed complete orbit locus. Applying this
to every irreducible component covers a reducible fixed chart without changing
its frame size, label, or scalar domain.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (B : (source p q I o).Opens)
  (hB : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ B = B)
  [IsAffine B.toScheme]
local notation "ρ" => restrictedAction (action e I o) B hB
attribute [local irreducible] source action restrictedAction Complete

/-- A complete interior anchor fills any preirreducible quotient subset containing it. -/
theorem complete_orbit_preirreducible_subset
    (Z : Set (quotient ρ)) (hZ : IsPreirreducible Z) (x : B.toScheme)
    (hx : B.ι x ∈ completeInterior (p := p) (q := q) I o)
    (hxZ : quotientMap ρ x ∈ Z) :
    Z ⊆ completeAffineOrbitImage e I o B hB := by
  obtain ⟨t, ht, hC⟩ := exists_complete_invariant_principal e I o B hB x hx
  let O : (quotient ρ).Opens := PrimeSpectrum.basicOpen t
  have hxO : quotientMap ρ x ∈ O := by
    change x ∈ quotientMap ρ ⁻¹ᵁ PrimeSpectrum.basicOpen t
    rwa [quotientMap_preimage_basicOpen]
  have hd := subset_closure_inter_of_isPreirreducible_of_isOpen hZ O.isOpen
    ⟨quotientMap ρ x, hxZ, hxO⟩
  apply hd.trans
  apply closure_minimal _ (completeAffineOrbitImage e I o B hB).isClosed
  rintro Q ⟨_, hQ⟩
  obtain ⟨y, rfl⟩ := (quotientMap ρ).surjective Q
  have hy : y ∈ B.toScheme.basicOpen t.val := by
    rw [← quotientMap_preimage_basicOpen]
    exact hQ
  exact ⟨y, completeInterior_subset I o (hC y hy), rfl⟩

/-- An interior anchor on each component covers every point of a fixed reducible chart. -/
theorem complete_fixed_chart_of_component_anchors
    (hanchors : ∀ Z ∈ irreducibleComponents (quotient ρ),
      ∃ x : B.toScheme, B.ι x ∈ completeInterior (p := p) (q := q) I o ∧
        quotientMap ρ x ∈ Z) :
    ∀ y : B.toScheme, B.ι y ∈ completePointLocus (p := p) (q := q) I o := by
  intro y
  let Z := irreducibleComponent (quotientMap ρ y)
  obtain ⟨x, hx, hxZ⟩ := hanchors Z (irreducibleComponent_mem_irreducibleComponents _)
  have hZ : IsPreirreducible Z := isIrreducible_irreducibleComponent.2
  have hm := complete_orbit_preirreducible_subset e I o B hB Z hZ x hx hxZ
    mem_irreducibleComponent
  change y ∈ B.ι ⁻¹' completePointLocus I o
  rw [← completeAffineOrbitImage_preimage e I o B hB]
  exact hm

end FLT.Mazur.EquivalenceRelationNormalizedFrames
