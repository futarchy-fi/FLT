/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOneGonLocalizedImages
public import FLT.Mazur.CubicMobiusClearing

/-!
# Unpunctured equations for the one-gon cubic

Faithful restriction descends the cleared Möbius equations to the localized
polynomial normalization. These equations can be evaluated at its endpoints.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonOneGonCubicCoordinates
open PolygonPinching PolygonNodeAffineCharts PolygonNodePresentation
open PolygonCubicSections PolygonPowerNodeEndpoints LocalizationJointRestriction
open OneGonTransition
variable (K : Type u) [Field K] (hn : 0 < 1)
  {C : Over (Spec (.of K))} (p : components K 1 ⟶ C) (q : nodes K 1 ⟶ C)
  (h : IsPushout (toComponents K 1 hn) (toNodes K 1) p q)
  (a : Fin 1 → Kˣ) (x : Spec (.of K)) (i : Fin 1)

local notation "s" => oneDenominator K hn p q h a x
local notation "c" => coordinate K hn p q h a x i
local notation "r" => restriction bPunctureMap s
local notation "g" => algebraMap (puncture K) (Localization.Away (bPunctureMap s))

/-- The cubic linear denominator in the original normalization parameter. -/
def normalizationDenominator : K[X] := X - Polynomial.C (a i : K) * (X - 1)

/-- The three cleared interpolation numerators on the polynomial normalization. -/
def normalizationNumerator (k : Fin 3) : K[X] :=
  if k = 0 then (X - 1) ^ 3 + Polynomial.C (weight K 1 a 3 i) * X ^ 3
  else if k = 1 then X * (X - 1) ^ 2 else X ^ 2 * (X - 1)

/-- The actual punctured ratios satisfy the polynomial equations. -/
lemma punctured_polynomial_equation (k : Fin 3) :
    r (c k) * g (algebraMap K[X] (puncture K) (normalizationDenominator K a i ^ 3)) =
      g (algebraMap K[X] (puncture K) (normalizationNumerator K a i k)) := by
  obtain ⟨_, h₀, h₁, h₂⟩ := punctured_parametrization K hn p q h a x i
  have hd : g (oneCanonicalDenominator K a i) * g (mobius K : puncture K) =
      (g (mobius K : puncture K) - g (algebraMap K (puncture K) (a i : K))) ^ 3 := by
    rw [← map_mul]
    simp only [oneCanonicalDenominator, mul_assoc, Units.inv_mul, mul_one,
      map_pow, map_sub]
  rw [hd] at h₀ h₁ h₂
  have ht := congrArg g (mobius_mul_difference K)
  rw [map_mul] at ht
  have hh := CubicMobiusClearing.equations _ _ _ _ _ _ _ _ ht h₀ h₁ h₂
  have hc (b : K) : algebraMap K[X] (puncture K) (Polynomial.C b) =
      algebraMap K (puncture K) b := (IsScalarTower.algebraMap_apply K K[X] _ b).symm
  fin_cases k
  · simpa [normalizationDenominator, normalizationNumerator, hc, difference_val,
      coordinate_val] using hh.1
  · simpa [normalizationDenominator, normalizationNumerator, hc, difference_val,
      coordinate_val] using hh.2.1
  · simpa [normalizationDenominator, normalizationNumerator, hc, difference_val,
      coordinate_val] using hh.2.2

/-- Descend the equations to the normalization before deleting either endpoint. -/
lemma normalization_equation (k : Fin 3) :
    NodeDenominatorRestriction.one s (c k) *
      algebraMap K[X] (Localization.Away (s).val) (normalizationDenominator K a i ^ 3) =
        algebraMap K[X] (Localization.Away (s).val) (normalizationNumerator K a i k) := by
  apply restriction_injective (algebraMap K[X] (puncture K)) (s).val
    NodePuncturedDenominatorRestriction.puncture_injective
  rw [map_mul, restriction_algebraMap, restriction_algebraMap]
  change NodePuncturedDenominatorRestriction.one s (c k) * _ = _
  rw [← PuncturedNodeRestrictionComparison.one_eq]
  exact punctured_polynomial_equation K hn p q h a x i k

end FLT.Mazur.PolygonOneGonCubicCoordinates
