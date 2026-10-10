/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationStages

/-!
# Exact realization of finite subideals by relation stages

A finitely generated subideal containing the old relations is represented
by a larger finite relation set, without adding any unintended equations.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationModel

universe u

variable {P : Type u} [CommRing P] (I : Ideal P)

/-- A finite subideal is exactly one cofinal finite relation stage. -/
theorem exists_relations_eq (s : Finset I) (J : Ideal P) (hJ : J.FG)
    (hs : relations I s ≤ J) (hI : J ≤ I) :
    ∃ t : Finset I, s ≤ t ∧ relations I t = J := by
  classical
  obtain ⟨v, hv⟩ := hJ
  have hm (x : P) (hx : x ∈ v) : x ∈ J := by
    rw [← hv]
    exact Ideal.subset_span hx
  let w : Finset I := v.attach.image fun x ↦ ⟨x.val, hI (hm x.val x.property)⟩
  refine ⟨s ∪ w, Finset.subset_union_left, le_antisymm ?_ ?_⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hs (Ideal.subset_span ⟨x, hx, rfl⟩)
    · obtain ⟨y, _, hxy⟩ := Finset.mem_image.mp hx
      have he : y.val = x.val := congrArg Subtype.val hxy
      exact he ▸ hm y.val y.property
  · rw [← hv]
    apply Ideal.span_le.mpr
    intro x hx
    let y : I := ⟨x, hI (hm x hx)⟩
    have hy : y ∈ w := Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩
    exact Ideal.subset_span ⟨y, Finset.mem_union_right _ hy, rfl⟩

end FLT.Mazur.FiniteRelationModel
