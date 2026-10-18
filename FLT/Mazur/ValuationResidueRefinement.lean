/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Refining a valuation by a valuation of its residue field

The inverse image of a residue valuation is a valuation in the original field.
It is contained in the original valuation, so every existing pole survives.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ValuationResidueRefinement
open IsLocalRing
variable {K : Type*} [Field K] (V : ValuationSubring K)
  (W : ValuationSubring (ResidueField V))

/-- Pull back the residue valuation, then include it in the original field. -/
def refinementRing : Subring K :=
  (W.toSubring.comap (residue V)).map V.subtype

/-- Membership retains an actual original valuation coordinate and its residue. -/
theorem mem_refinementRing (x : K) :
    x ∈ refinementRing V W ↔ ∃ a : V, (a : K) = x ∧ residue V a ∈ W := by
  constructor
  · rintro ⟨a, ha, hax⟩
    exact ⟨a, hax, ha⟩
  · rintro ⟨a, rfl, ha⟩
    exact ⟨a, ha, rfl⟩

/-- Pullback along the residue map satisfies the valuation alternative. -/
theorem refinementRing_mem_or_inv (x : K) :
    x ∈ refinementRing V W ∨ x⁻¹ ∈ refinementRing V W := by
  by_cases hx : x ∈ V
  · let a : V := ⟨x, hx⟩
    by_cases ha : residue V a ∈ W
    · exact Or.inl ((mem_refinementRing V W x).mpr ⟨a, rfl, ha⟩)
    · have hn : residue V a ≠ 0 := fun h ↦ ha (h ▸ W.zero_mem)
      have hu : IsUnit a := (residue_ne_zero_iff_isUnit a).mp hn
      obtain ⟨u, hu⟩ := hu
      have hi : ((↑(u⁻¹) : V) : K) = x⁻¹ := by
        change V.subtype (↑(u⁻¹)) = x⁻¹
        rw [map_units_inv, hu]
        rfl
      refine Or.inr ((mem_refinementRing V W (x⁻¹)).mpr ⟨↑(u⁻¹), hi, ?_⟩)
      have hres : residue V (↑(u⁻¹)) = (residue V a)⁻¹ := by
        rw [← hu]
        exact map_units_inv (residue V) u
      rw [hres]
      exact (W.mem_or_inv_mem (residue V a)).resolve_left ha
  · have hi := (V.mem_or_inv_mem x).resolve_left hx
    let a : V := ⟨x⁻¹, hi⟩
    have hm : a ∈ maximalIdeal V :=
      V.coe_mem_nonunits_iff.mp (V.inv_mem_nonunits_iff.mpr (Or.inr hx))
    exact Or.inr ((mem_refinementRing V W (x⁻¹)).mpr
      ⟨a, rfl, by rw [(residue_eq_zero_iff a).mpr hm]; exact W.zero_mem⟩)

/-- The composite valuation in the original ambient field. -/
def refinement : ValuationSubring K where
  toSubring := refinementRing V W
  mem_or_inv_mem' := refinementRing_mem_or_inv V W

/-- Refinement can only remove regular elements. -/
theorem refinement_le : refinement V W ≤ V := by
  intro x hx
  obtain ⟨a, rfl, _⟩ := (mem_refinementRing V W x).mp hx
  exact a.property

/-- Every original pole remains a pole after residue refinement. -/
theorem not_mem_refinement {x : K} (hx : x ∉ V) : x ∉ refinement V W :=
  fun h ↦ hx (refinement_le V W h)

end FLT.Mazur.ValuationResidueRefinement
