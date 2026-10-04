/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOneGonPolynomialEquations
public import FLT.Mazur.PolygonNodeEqualizerComparison

/-!
# The one-gon refinement denominator is nonzero at the node

Evaluate the cleared equations on the unpunctured normalization. The two
interior coordinates vanish and the node coordinate is nonzero, so the
quadratic refinement denominator has nonzero value minus its square.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonOneGonCubicCoordinates
open PolygonPinching PolygonNodeAffineCharts PolygonNodePresentation PolygonCubicSections
variable (K : Type u) [Field K] (hn : 0 < 1)
  {C : Over (Spec (.of K))} (p : components K 1 ⟶ C) (q : nodes K 1 ⟶ C)
  (h : IsPushout (toComponents K 1 hn) (toNodes K 1) p q)
  (a : Fin 1 → Kˣ) (x : Spec (.of K)) (i : Fin 1)

local notation "s" => oneDenominator K hn p q h a x
local notation "c" => coordinate K hn p q h a x i

/-- Evaluation on the exact localized pinched ring, through its normalization. -/
def nodeEvaluation : Localization.Away s →+* K :=
  (OneGonDenominatorEqualizer.evalZero s
    (oneDenominator_value_isUnit K hn p q h a x)).comp (NodeDenominatorRestriction.one s)

/-- The actual interpolation coordinates at the node. -/
lemma nodeEvaluation_coordinates :
    nodeEvaluation K hn p q h a x (c 0) * (a i : K) ^ 3 = -1 ∧
    nodeEvaluation K hn p q h a x (c 1) = 0 ∧
    nodeEvaluation K hn p q h a x (c 2) = 0 := by
  have he (k : Fin 3) := congrArg (OneGonDenominatorEqualizer.evalZero s
    (oneDenominator_value_isUnit K hn p q h a x))
      (normalization_equation K hn p q h a x i k)
  have h₀ := he 0
  have h₁ := he 1
  have h₂ := he 2
  simp only [map_mul, OneGonDenominatorEqualizer.evalZero,
    NodeDenominatorEqualizer.evaluation_algebraMap] at h₀ h₁ h₂
  have ha : (a i : K) ^ 3 ≠ 0 := pow_ne_zero _ (a i).ne_zero
  refine ⟨?_, ?_, ?_⟩
  · simpa [nodeEvaluation, OneGonDenominatorEqualizer.evalZero, normalizationDenominator,
      normalizationNumerator, show (-1 : K) ^ 3 = -1 by ring] using h₀
  · apply (mul_eq_zero.mp (show nodeEvaluation K hn p q h a x (c 1) *
        (a i : K) ^ 3 = 0 by
          simpa [nodeEvaluation, OneGonDenominatorEqualizer.evalZero, normalizationDenominator,
      normalizationNumerator, show (-1 : K) ^ 3 = -1 by ring] using h₁)).resolve_right ha
  · apply (mul_eq_zero.mp (show nodeEvaluation K hn p q h a x (c 2) *
        (a i : K) ^ 3 = 0 by
          simpa [nodeEvaluation, OneGonDenominatorEqualizer.evalZero, normalizationDenominator,
      normalizationNumerator, show (-1 : K) ^ 3 = -1 by ring] using h₂)).resolve_right ha

/-- The exact quadratic used for source refinement is nonzero at the node. -/
lemma nodeEvaluation_refinement_isUnit :
    IsUnit (nodeEvaluation K hn p q h a x
      (chartAlgMap K hn p q h a x (sourceDenominator K a i))) := by
  obtain ⟨h₀, h₁, h₂⟩ := nodeEvaluation_coordinates K hn p q h a x i
  have hc : nodeEvaluation K hn p q h a x (c 0) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h₀
    exact neg_ne_zero.mpr one_ne_zero h₀.symm
  rw [map_sourceDenominator]
  simp only [OneGonCubicElimination.denominator, map_add, map_sub, map_neg, map_mul,
    map_pow, map_ofNat, map_one, h₁, h₂, zero_pow (by decide : 2 ≠ 0),
    mul_zero, add_zero, sub_zero]
  exact isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (pow_ne_zero _ hc))

end FLT.Mazur.PolygonOneGonCubicCoordinates
