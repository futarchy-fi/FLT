/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointNumeratorLaurentOverlap
public import FLT.Mazur.LaurentUnitMarkingCancellation

/-!
# Exact coefficient transitions at the original marked Laurent edge

Cancel the actual regular marking equation before any coefficient reduction.
The retained numerator on the incoming chart is the outgoing numerator times
the prescribed signed Laurent monomial; every lower coefficient is included.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing FCurve LaurentPolynomial ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj ModuleSheafTensor.tensor divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i : Fin n)
local notation "t" => parameter K m
local notation "p" => Equiv.symm (finRotate n) i
local notation "L" => originalStageSinglePointLine K n h m i
local notation "N" => completePointStageChartNumerator K n h m i

/-- At the marking, cross multiplication uses exactly T-1 and T⁻¹-1. -/
theorem completePointStageNumerator_marked_cross (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) :
    (T 1 - 1) ^ d * precedingLaurentMap (Ring K m) (t) (N (p) d s) =
      (T (-1) - 1) ^ d * leftLaurentMap (t) (N i d s) := by
  simpa only [PolygonInfinitesimal.chartMarkingEquation, PolygonCyclicAtlas.prev_ne h i,
    ite_true, ite_false, inv_one, Units.val_one, map_sub, map_one,
    leftLaurentMap_left, precedingLaurentMap_right] using
    completePointStageChartNumerator_laurent K n h m i i d s

/-- Regular cancellation gives the precise transition for the original numerator. -/
theorem completePointStageNumerator_marked_transition (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) :
    precedingLaurentMap (Ring K m) (t) (N (p) d s) =
      (-T (-1)) ^ d * leftLaurentMap (t) (N i d s) :=
  LaurentUnitMarking.numerator_transition (Ring K m) d _ _
    (completePointStageNumerator_marked_cross K n h m i d s)

/-- All original numerator coefficients obey the signed degree shift over the full stage ring. -/
theorem completePointStageNumerator_marked_coefficient (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) (k : ℤ) :
    (precedingLaurentMap (Ring K m) (t) (N (p) d s)).coeff k =
      (-1 : Ring K m) ^ d * (leftLaurentMap (t) (N i d s)).coeff (k + d) :=
  LaurentUnitMarking.numerator_transition_coefficient (Ring K m) d _ _
    (completePointStageNumerator_marked_cross K n h m i d s) k

end FLT.Mazur.PolygonInfinitesimalStages
