/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
# Semistability from integral unit invariants

An integral equation with unit discriminant is already minimal. Together
with the existing unit-c₄ minimality criterion, this identifies integral
unit-invariant models with actual good or multiplicative reduction.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing IsDedekindDomain.HeightOneSpectrum

universe u

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- An integral equation with unit-valued discriminant is minimal. -/
theorem isMinimal_of_valuation_discriminant_eq_one (E : WeierstrassCurve K)
    [IsIntegral R E] (hΔ : valuation K (IsDiscreteValuationRing.maximalIdeal R) E.Δ = 1) :
    IsMinimal R E := by
  refine ⟨⟨by simpa using (inferInstance : IsIntegral R E), ?_⟩⟩
  intro C _ _
  apply Subtype.coe_le_coe.mp
  simpa only [one_smul, valuation_Δ_aux_eq_of_isIntegral, hΔ] using
    (valuation_Δ_aux R (C • E)).property

/-- Unit discriminant or unit c₄ supplies both minimality and the semistable reduction predicate. -/
theorem good_or_multiplicative_of_unit_invariants (W : WeierstrassCurve R)
    (h : IsUnit W.Δ ∨ IsUnit W.c₄) :
    (W.map (algebraMap R K)).HasGoodReduction R ∨
      (W.map (algebraMap R K)).HasMultiplicativeReduction R := by
  have : IsIntegral R (W.map (algebraMap R K)) := ⟨⟨W, rfl⟩⟩
  have hunit (x : R) (hx : IsUnit x) :
      valuation K (IsDiscreteValuationRing.maximalIdeal R) (algebraMap R K x) = 1 := by
    rw [valuation_eq_one_iff_notMem]
    change x ∉ maximalIdeal R
    simpa only [mem_maximalIdeal, mem_nonunits_iff, not_not] using hx
  by_cases hd : IsUnit W.Δ
  · have hv : valuation K (IsDiscreteValuationRing.maximalIdeal R)
        (W.map (algebraMap R K)).Δ = 1 := by rw [map_Δ]; exact hunit W.Δ hd
    have : IsMinimal R (W.map (algebraMap R K)) :=
      isMinimal_of_valuation_discriminant_eq_one _ hv
    exact Or.inl { goodReduction := hv }
  · have hc : IsUnit W.c₄ := h.resolve_left hd
    have hv : valuation K (IsDiscreteValuationRing.maximalIdeal R)
        (W.map (algebraMap R K)).c₄ = 1 := by rw [map_c₄]; exact hunit W.c₄ hc
    have : IsMinimal R (W.map (algebraMap R K)) := isMinimal_of_valuation_c₄_eq_one R _ hv
    refine Or.inr { multiplicativeReduction := hv, badReduction := ?_ }
    rw [map_Δ]
    apply (valuation_lt_one_iff_mem _ _).mpr
    change W.Δ ∈ maximalIdeal R
    simpa only [mem_maximalIdeal, mem_nonunits_iff] using hd

end FLT.Mazur
