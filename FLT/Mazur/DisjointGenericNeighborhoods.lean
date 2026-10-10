/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowGenericNeighborhoods

/-!
# Simultaneous disjoint neighborhoods of all component generic points

In a Noetherian scheme each component has an open part disjoint from the other
components. Intersecting these parts with prescribed generic neighborhoods
produces pairwise disjoint opens whose union is dense.
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace Set

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace FLT.Mazur.DisjointGenericNeighborhoods

variable {X : Scheme} [NoetherianSpace X]

/-- The open part of a component remaining after all other components are removed. -/
def componentOpen (C : irreducibleComponents X) : X.Opens :=
  ⟨(⋃₀ (irreducibleComponents X \ {C.val}))ᶜ,
    by
      rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
      exact NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
        fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1⟩

/-- The exclusive open part lies inside its component. -/
lemma componentOpen_subset (C : irreducibleComponents X) :
    (componentOpen C : Set X) ⊆ C := by
  have h := closure_sUnion_irreducibleComponents_sdiff_singleton
    NoetherianSpace.finite_irreducibleComponents C.val C.property
  exact subset_closure.trans h.le

/-- The component generic point belongs to its exclusive open part. -/
lemma generic_mem_componentOpen (C : irreducibleComponents X) :
    (genericPoints.ofComponent C).val ∈ componentOpen C := by
  rintro ⟨W, ⟨hW, hne⟩, hηW⟩
  have hCW : C.val ⊆ W :=
    ((genericPoints.isGenericPoint_ofComponent C).mem_closed_set_iff
      (isClosed_of_mem_irreducibleComponents W hW)).mp hηW
  have he : W = C.val := (C.property.2 hW.1 hCW).antisymm hCW
  exact hne (Set.mem_singleton_iff.mpr he)

/-- Exclusive component opens are pairwise disjoint. -/
lemma componentOpen_disjoint : Pairwise (fun C D : irreducibleComponents X ↦
    Disjoint (componentOpen C) (componentOpen D)) := by
  intro C D hCD
  rw [← Opens.coe_disjoint]
  apply Set.disjoint_left.mpr
  intro x hxC hxD
  exact hxC ⟨D.val, ⟨D.property, fun he ↦ hCD
    (Subtype.ext (Set.mem_singleton_iff.mp he).symm)⟩, componentOpen_subset D hxD⟩

/-- Prescribed neighborhoods of all generic points have disjoint refinements. -/
theorem exists_disjoint_refinement (W : genericPoints X → X.Opens)
    (hW : ∀ η, η.val ∈ W η) :
    ∃ V : genericPoints X → X.Opens,
      (∀ η, V η ≤ W η) ∧ (∀ η, η.val ∈ V η) ∧
      Pairwise (fun η ξ ↦ Disjoint (V η) (V ξ)) ∧
      genericPoints X ⊆ (iSup V : X.Opens) ∧ Dense (↑(iSup V : X.Opens) : Set X) := by
  let V (η : genericPoints X) := componentOpen (genericPoints.component η) ⊓ W η
  have hV (η : genericPoints X) : η.val ∈ V η := by
    refine ⟨?_, hW η⟩
    have h := generic_mem_componentOpen (genericPoints.component η)
    rw [genericPoints.ofComponent_component] at h
    exact h
  have hd : Pairwise (fun η ξ ↦ Disjoint (V η) (V ξ)) := by
    intro η ξ hne
    exact (componentOpen_disjoint (fun he ↦ hne (genericPoints.component_injective he))).mono
      inf_le_left inf_le_left
  have hg : genericPoints X ⊆ (iSup V : X.Opens) := by
    intro η hη
    exact Opens.mem_iSup.mpr ⟨⟨η, hη⟩, hV ⟨η, hη⟩⟩
  exact ⟨V, fun _ ↦ inf_le_right, hV, hd, hg,
    (dense_iff_closure_eq.mpr genericPoints.closure).mono hg⟩

end FLT.Mazur.DisjointGenericNeighborhoods
