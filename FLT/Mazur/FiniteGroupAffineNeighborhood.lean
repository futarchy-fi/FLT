/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleFiniteAffineNeighborhood
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Invariant affine neighborhoods of finite orbits

Intersect the translates of a common affine neighborhood. Separatedness makes
the finite intersection affine, and the entire orbit remains inside it.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteGroupNeighborhood

universe u
variable {G : Type*} [Group G] [Finite G] {X : Scheme.{u}} (ρ : G →* Aut X)

/-- The open contained in every translate of an open neighborhood. -/
def invariantCore (U : X.Opens) : X.Opens := ⨅ g : G, (ρ g).hom ⁻¹ᵁ U

/-- Membership means that the entire orbit is in the original open. -/
lemma mem_invariantCore (U : X.Opens) (x : X) :
    x ∈ invariantCore ρ U ↔ ∀ g : G, (ρ g).hom x ∈ U := by
  change x ∈ ((invariantCore ρ U : X.Opens) : Set X) ↔ _
  simp only [invariantCore, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  rfl

/-- The identity translate bounds the invariant core by the original open. -/
lemma invariantCore_le (U : X.Opens) : invariantCore ρ U ≤ U := by
  intro x hx
  have h := (mem_invariantCore ρ U x).mp hx 1
  rw [map_one] at h
  exact h

omit [Finite G] in
/-- Composition of the actual automorphisms agrees with the group product. -/
lemma action_mul_apply (g h : G) (x : X) :
    (ρ g).hom ((ρ h).hom x) = (ρ (g * h)).hom x := by
  rw [map_mul]
  rfl

/-- The core is stable under every group element, with equality of opens. -/
lemma invariantCore_preimage (U : X.Opens) (h : G) :
    (ρ h).hom ⁻¹ᵁ invariantCore ρ U = invariantCore ρ U := by
  ext x
  change (ρ h).hom x ∈ invariantCore ρ U ↔ x ∈ invariantCore ρ U
  simp only [mem_invariantCore, action_mul_apply]
  constructor
  · intro hx g
    simpa only [inv_mul_cancel_right] using hx (g * h⁻¹)
  · intro hx g
    exact hx (g * h)

/-- A finite intersection of affine translates is affine on a separated scheme. -/
lemma isAffineOpen_invariantCore [X.IsSeparated] (U : X.Opens) (hU : IsAffineOpen U) :
    IsAffineOpen (invariantCore ρ U) :=
  IsAffineOpen.iInf fun g ↦ hU.preimage_of_isIso (ρ g).hom

/-- Every orbit has an invariant affine neighborhood on a separated ample scheme. -/
theorem exists_invariant_affine [X.IsSeparated] (L : X.Modules)
    [Fact (FCurve.LocallyFreeRankOne L)] (hL : FCurve.AmpleLineBundle L) (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U := by
  classical
  let _ := Fintype.ofFinite G
  obtain ⟨V, hV, hVs, _⟩ := AmpleFiniteNeighborhood.of_ample L hL ⊤
    (Finset.univ.image fun g : G ↦ (ρ g).hom x) (by simp)
  refine ⟨invariantCore ρ V, isAffineOpen_invariantCore ρ V hV, ?_,
    invariantCore_preimage ρ V⟩
  rw [mem_invariantCore]
  intro g
  exact hVs _ (Finset.mem_image.mpr ⟨g, Finset.mem_univ g, rfl⟩)

end FLT.Mazur.FiniteGroupNeighborhood
