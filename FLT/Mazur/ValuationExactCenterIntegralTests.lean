/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ValuationLocalRefinement
public import FLT.Mazur.ValuationSubringIntegralTests

/-!
# Integral closure tested at the exact local center

Refining a nonintegrality witness through its residue field makes the scalar
map local without losing the coordinate pole. Thus valuations with the exact
local center already detect integral closure, including for noninjective scalars.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ValuationSubringIntegralTests
open IsLocalRing ValuationResidueRefinement
variable {R K : Type*} [CommRing R] [IsLocalRing R] [Field K]
  (s : R →+* K) (x : K)

/-- Nonintegrality constructs a valuation pole with a local scalar map. -/
theorem exists_local_valuation_of_not_integral (h : ¬ s.IsIntegralElem x) :
    ∃ (V : ValuationSubring K) (f : R →+* V),
      V.subtype.comp f = s ∧ IsLocalHom f ∧ x ∉ V := by
  obtain ⟨V, hV, hx⟩ := exists_valuation_of_not_integral s x h
  let f : R →+* V := s.codRestrict V.toSubring (fun a ↦ hV ⟨a, rfl⟩)
  obtain ⟨V', f', hf', hl, hx'⟩ := exists_local_refinement_with_pole V f x hx
  exact ⟨V', f', hf', hl, hx'⟩

/-- The constructed center is exactly the maximal ideal of the original local scalar ring. -/
theorem exists_exact_center_valuation_of_not_integral (h : ¬ s.IsIntegralElem x) :
    ∃ (V : ValuationSubring K) (f : R →+* V),
      V.subtype.comp f = s ∧ (maximalIdeal V).comap f = maximalIdeal R ∧ x ∉ V := by
  obtain ⟨V, f, hf, hl, hx⟩ := exists_local_valuation_of_not_integral s x h
  let _ := hl
  exact ⟨V, f, hf, maximalIdeal_comap f, hx⟩

/-- It suffices to test scalar-compatible valuations with local scalar maps. -/
theorem integralElem_iff_local_valuations :
    s.IsIntegralElem x ↔ ∀ (V : ValuationSubring K) (f : R →+* V),
      V.subtype.comp f = s → IsLocalHom f → x ∈ V := by
  refine ⟨fun hi V f hf _ ↦ ?_, fun h ↦ ?_⟩
  · apply (integralElem_iff_valuation_subrings s x).mp hi V
    rintro _ ⟨a, rfl⟩
    rw [← hf]
    exact (f a).property
  · by_contra hn
    obtain ⟨V, f, hf, hl, hx⟩ := exists_local_valuation_of_not_integral s x hn
    exact hx (h V f hf hl)

/-- Equivalently, prescribe the exact maximal-ideal contraction explicitly. -/
theorem integralElem_iff_exact_center_valuations :
    s.IsIntegralElem x ↔ ∀ (V : ValuationSubring K) (f : R →+* V),
      V.subtype.comp f = s → (maximalIdeal V).comap f = maximalIdeal R → x ∈ V := by
  refine ⟨fun hi V f hf _ ↦ ?_, fun h ↦ ?_⟩
  · apply (integralElem_iff_valuation_subrings s x).mp hi V
    rintro _ ⟨a, rfl⟩
    rw [← hf]
    exact (f a).property
  · by_contra hn
    obtain ⟨V, f, hf, hc, hx⟩ := exists_exact_center_valuation_of_not_integral s x hn
    exact hx (h V f hf hc)

end FLT.Mazur.ValuationSubringIntegralTests
