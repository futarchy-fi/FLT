/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Affine neighborhoods containing component generic points

We prove the Noetherian case of Stacks 01ZX, sufficient for Chow's construction
over a Noetherian base. In fact only the underlying topological space needs
to be Noetherian. A component generic point missing an open also misses its
closure. This gives a disjoint affine neighborhood, and finite induction
enlarges any affine open to contain any finite set of component generic points.

The shrinking step uses finiteness of the irreducible components. It does not
establish the more general quasi-separated version of Stacks 01ZX. Stacks
01ZY concerns arbitrary finite sets under additional geometric assumptions;
here the finite set consists specifically of component generic points.
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace FLT.Mazur.Chow

/-- In a Noetherian space, a component generic point belongs to the closure of
an open exactly when it belongs to that open. -/
lemma generic_mem_closure_open_iff {T : Type*} [TopologicalSpace T]
    [NoetherianSpace T] {η : T} (hη : η ∈ genericPoints T)
    {U : Set T} (hU : IsOpen U) : η ∈ closure U ↔ η ∈ U := by
  refine ⟨fun h ↦ ?_, fun h ↦ subset_closure h⟩
  obtain ⟨V, hV, hne, hsub⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (closure ({η} : Set T)) hη
  have hg : IsGenericPoint η (closure ({η} : Set T)) := isGenericPoint_closure
  have hηV : η ∈ V := by
    obtain ⟨y, hy⟩ := hne
    exact (hg.specializes (hsub hy)).mem_open hV hy
  obtain ⟨y, hyV, hyU⟩ := mem_closure_iff.mp h V hV hηV
  exact (hg.specializes (hsub hyV)).mem_open hU hyU

variable {X : Scheme.{u}} [NoetherianSpace X]

/-- Shrink any open neighborhood of a component generic point to an affine
neighborhood disjoint from an open missing that point. In the Noetherian
case all opens are compact, so no separate compactness input is needed. -/
lemma exists_affine_generic_disjoint (η : X) (hη : η ∈ genericPoints X)
    (U W : X.Opens) (hηU : η ∉ U) (hηW : η ∈ W) :
    ∃ V : X.Opens, IsAffineOpen V ∧ η ∈ V ∧ V ≤ W ∧ Disjoint U V := by
  let O : X.Opens := ⟨(closure (U : Set X))ᶜ, isClosed_closure.isOpen_compl⟩
  have hηO : η ∈ O := by
    exact fun h ↦ hηU ((generic_mem_closure_open_iff hη U.isOpen).mp h)
  obtain ⟨V, hV, hηV, hVO⟩ :=
    exists_isAffineOpen_mem_and_subset (U := W ⊓ O) ⟨hηW, hηO⟩
  refine ⟨V, hV, hηV, hVO.trans inf_le_left, ?_⟩
  rw [← Opens.coe_disjoint]
  exact Set.disjoint_left.mpr fun y hyU hyV ↦ (hVO hyV).2 (subset_closure hyU)

/-- An affine open can be enlarged to contain one more component generic point. -/
lemma exists_affine_sup_generic (U : X.Opens) (hU : IsAffineOpen U)
    (η : X) (hη : η ∈ genericPoints X) :
    ∃ V : X.Opens, IsAffineOpen V ∧ U ≤ V ∧ η ∈ V := by
  by_cases hηU : η ∈ U
  · exact ⟨U, hU, le_rfl, hηU⟩
  · obtain ⟨W, hW, hηW, _, hd⟩ :=
      exists_affine_generic_disjoint η hη U ⊤ hηU (by trivial)
    exact ⟨U ⊔ W, hU.sup_of_disjoint hW hd, le_sup_left, Or.inr hηW⟩

/-- Enlarge an affine open to contain a finite set of component generic points.
The resulting neighborhood is constructed using finite disjoint affine unions. -/
theorem exists_affine_sup_finite_generics (U : X.Opens) (hU : IsAffineOpen U)
    (s : Set X) (hs : s.Finite) (hg : s ⊆ genericPoints X) :
    ∃ V : X.Opens, IsAffineOpen V ∧ U ≤ V ∧ s ⊆ V := by
  classical
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨U, hU, le_rfl, Set.empty_subset _⟩
  | @insert η s hη hs ih =>
    obtain ⟨V, hV, hUV, hsV⟩ := ih (fun y hy ↦ hg (Set.mem_insert_of_mem η hy))
    obtain ⟨W, hW, hVW, hηW⟩ := exists_affine_sup_generic V hV η (hg (by simp))
    refine ⟨W, hW, hUV.trans hVW, ?_⟩
    exact Set.insert_subset hηW (hsV.trans hVW)

/-- Stacks 01ZX for schemes with Noetherian underlying space: every point has
an affine neighborhood containing any prescribed finite set of component
generic points. No affine neighborhood is supplied as input. -/
theorem exists_affine_mem_finite_generics (x : X) (s : Set X) (hs : s.Finite)
    (hg : s ⊆ genericPoints X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ s ⊆ U := by
  obtain ⟨V, hV, hxV, _⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by trivial)
  obtain ⟨U, hU, hVU, hsU⟩ := exists_affine_sup_finite_generics V hV s hs hg
  exact ⟨U, hU, hVU hxV, hsU⟩

/-- In the Noetherian case, one affine neighborhood contains the point and
every component generic point, including when there are several components. -/
theorem exists_affine_mem_all_generics (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ genericPoints X ⊆ U :=
  exists_affine_mem_finite_generics x (genericPoints X)
    (genericPoints.finite NoetherianSpace.finite_irreducibleComponents) Set.Subset.rfl

end FLT.Mazur.Chow
