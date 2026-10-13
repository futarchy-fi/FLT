/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOpenEnvelopeLocus
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Finite faithful neighborhoods inside prescribed branch opens

A finite etale map allows shrinking its base so that the whole source lies
in a given open containing the chosen fiber. The base is principal affine
and the restricted map is finite, etale and surjective. No points from the
retained fibers are discarded.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteEtaleWholeFiberNeighborhood
open SchemeOpenEnvelope
universe u
variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsAffine Y] [IsFinite g] [Etale g]

/-- A principal base neighborhood retains full fibers inside the prescribed source open. -/
theorem exists_principal (x : X) (U : X.Opens)
    (hU : ∀ z : X, g z = g x → z ∈ U) :
    ∃ r : Γ(Y, ⊤), g x ∈ Y.basicOpen r ∧ g ⁻¹ᵁ Y.basicOpen r ≤ U ∧
      (Y.basicOpen r : Set Y) ⊆ Set.range g := by
  let W := fullFiberOpen g U g.isClosedMap
  let I : Y.Opens := ⟨Set.range g, g.isOpenMap.isOpen_range⟩
  have hx : g x ∈ W ⊓ I := ⟨(mem_fullFiberLocus g U (g x)).mpr hU, ⟨x, rfl⟩⟩
  obtain ⟨r, hr, hsub⟩ := AffineEnvelopeFiniteNeighborhood.exists_envelope_principal
    (W ⊓ I) {g x} (Set.finite_singleton _) (Set.singleton_subset_iff.mpr hx)
  refine ⟨r, hr rfl, ?_, fun y hy ↦ (hsub hy).2⟩
  intro z hz
  exact preimage_fullFiberOpen_le g U g.isClosedMap (hsub hz).1

omit [IsAffine Y] [IsFinite g] [Etale g] in
/-- Range containment proves surjectivity of the actual whole-fiber base restriction. -/
theorem restrict_surjective (r : Γ(Y, ⊤))
    (hr : (Y.basicOpen r : Set Y) ⊆ Set.range g) : Surjective (g ∣_ Y.basicOpen r) := by
  constructor
  intro y
  obtain ⟨z, hz⟩ := hr y.property
  refine ⟨⟨z, show g z ∈ Y.basicOpen r from hz ▸ y.property⟩, ?_⟩
  apply (Y.basicOpen r).ι.isOpenEmbedding.injective
  change ((g ∣_ Y.basicOpen r) ≫ (Y.basicOpen r).ι) _ = _
  rw [morphismRestrict_ι]
  exact hz

/-- The constructed neighborhood is affine, finite, etale and faithfully covers its base. -/
theorem exists_finite_faithful_restriction (x : X) (U : X.Opens)
    (hU : ∀ z : X, g z = g x → z ∈ U) :
    ∃ r : Γ(Y, ⊤), g x ∈ Y.basicOpen r ∧ g ⁻¹ᵁ Y.basicOpen r ≤ U ∧
      IsAffine (g ⁻¹ᵁ Y.basicOpen r).toScheme ∧
      IsFinite (g ∣_ Y.basicOpen r) ∧ Etale (g ∣_ Y.basicOpen r) ∧
      Surjective (g ∣_ Y.basicOpen r) := by
  obtain ⟨r, hx, hU, hr⟩ := exists_principal g x U hU
  have hA : IsAffineOpen (Y.basicOpen r) := (isAffineOpen_top Y).basicOpen r
  have hX : IsAffineOpen (g ⁻¹ᵁ Y.basicOpen r) := hA.preimage g
  exact ⟨r, hx, hU, hX, inferInstance, inferInstance, restrict_surjective g r hr⟩

/-- A single-point base fiber allows any neighborhood of that point to be used. -/
theorem exists_finite_faithful_restriction_of_unique (x : X)
    (huniq : ∀ z : X, g z = g x → z = x) (U : X.Opens) (hx : x ∈ U) :
    ∃ r : Γ(Y, ⊤), g x ∈ Y.basicOpen r ∧ g ⁻¹ᵁ Y.basicOpen r ≤ U ∧
      IsAffine (g ⁻¹ᵁ Y.basicOpen r).toScheme ∧
      IsFinite (g ∣_ Y.basicOpen r) ∧ Etale (g ∣_ Y.basicOpen r) ∧
      Surjective (g ∣_ Y.basicOpen r) :=
  exists_finite_faithful_restriction g x U (fun z hz ↦ huniq z hz ▸ hx)

end FLT.Mazur.FiniteEtaleWholeFiberNeighborhood
