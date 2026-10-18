/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Reciprocal certificates for a pole over a valuation ring

An element outside a valuation ring has an inverse in its maximal ideal.
This gives an explicit multiplication equation in the unchanged fraction
field and a reciprocal which vanishes at the closed point.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ValuationPoleReciprocal
variable (V K : Type*) [CommRing V] [IsDomain V] [ValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]

/-- A pole has a reciprocal in the maximal ideal, with the exact fraction-field equation. -/
theorem exists_reciprocal (x : K) (h : x ∉ (algebraMap V K).range) :
    ∃ v : V, v ∈ IsLocalRing.maximalIdeal V ∧ algebraMap V K v * x = 1 := by
  have hx : x ≠ 0 := fun hx ↦ h (hx ▸ (algebraMap V K).range.zero_mem)
  obtain ⟨v, hv⟩ := (ValuationRing.isInteger_or_isInteger V x).resolve_left h
  refine ⟨v, ?_, by rw [hv, inv_mul_cancel₀ hx]⟩
  change ¬ IsUnit v
  intro hu
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
  apply h
  refine ⟨w, ?_⟩
  have he : x⁻¹ * algebraMap V K w = 1 := by
    rw [← hv, ← map_mul, hw, map_one]
  calc
    algebraMap V K w = x * (x⁻¹ * algebraMap V K w) := by
      rw [← mul_assoc, mul_inv_cancel₀ hx, one_mul]
    _ = x := by rw [he, mul_one]

/-- The reciprocal certificate specializes to zero in the valuation ring's residue field. -/
theorem exists_residue_zero_reciprocal (x : K) (h : x ∉ (algebraMap V K).range) :
    ∃ v : V, IsLocalRing.residue V v = 0 ∧ algebraMap V K v * x = 1 := by
  obtain ⟨v, hv, he⟩ := exists_reciprocal V K x h
  exact ⟨v, Ideal.Quotient.eq_zero_iff_mem.mpr hv, he⟩

end FLT.Mazur.ValuationPoleReciprocal
