/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointNodeLocalization
public import FLT.Mazur.PolygonSmoothingLocalizedPolynomials

/-!
# Common polynomial numerators for the particular original pole functions

The two functions retained from the complete cubic have a common power of the
specified node denominator. This supplies polynomial representatives, not a
calculation or normalization of their still undetermined coefficients.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i j : Fin n)
local notation "t" => parameter K m
local notation "d" => algebraMap (ChartRing (t)) (StageNodeLocalization K m)
  (nodeMarkingDenominator (t))
local notation "P" => nodeLocalizedPolynomialMap (t)

/-- The actual two retained pole functions have simultaneous original polynomial numerators. -/
theorem completePointNodePoleNumerators_exist :
    ∃ (r : ℕ) (p q : MvPolynomial (Fin 2) (Ring K m)),
      completePointNodeLocalizedPoleTwo K n h m i j * (d) ^ r = (P) p ∧
        completePointNodeLocalizedPoleThree K n h m i j * (d) ^ r = (P) q :=
  nodeLocalizedPolynomial_pair (t) _ _

/-- Clearing that same denominator gives the original cubic triple [p,q,d^r]. -/
theorem completePointNodeCubic_numerators
    (r : ℕ) (p q : MvPolynomial (Fin 2) (Ring K m))
    (hp : completePointNodeLocalizedPoleTwo K n h m i j * (d) ^ r = (P) p)
    (hq : completePointNodeLocalizedPoleThree K n h m i j * (d) ^ r = (P) q)
    (k : Fin 3) :
    completePointNodeLocalizationMap K n h m i j
        (completePointStageNodeCubic K n h m i j k) * (d) ^ r =
      (P) (![p, q, nodeMarkingDenominatorPolynomial ^ r] k) := by
  rw [completePointNodeLocalizedCubic_coordinates]
  fin_cases k
  · exact hp
  · exact hq
  · change 1 * (d) ^ r = (P) (nodeMarkingDenominatorPolynomial ^ r)
    rw [one_mul, map_pow, nodeLocalizedPolynomialMap_denominator]

end FLT.Mazur.PolygonInfinitesimalStages
