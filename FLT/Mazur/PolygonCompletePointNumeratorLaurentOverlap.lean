/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorAffineNumeratorOverlap
public import FLT.Mazur.PolygonCompletePointStageBoundedNumerators

/-!
# Full Laurent overlap equations for the retained chart numerators

The original cyclic gluing compares the actual bounded numerators of the
same retained section. The equation is in the full arithmetic Laurent ring,
including the marking and every nilpotent coefficient.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing FCurve AffineImmersionSectionCoordinates
open ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj ModuleSheafTensor.tensor divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i j : Fin n)
local notation "t" => parameter K m
local notation "p" => Equiv.symm (finRotate n) j
local notation "f" k => PolygonInfinitesimal.chart (Ring K m) (t) n h k
local notation "a" k => PolygonInfinitesimal.chartMarkingEquation (Ring K m) (t) n i k 1
local notation "g" k => PolygonInfinitesimal.markingImageEquation (Ring K m) (t) n h i k 1
local notation "hI" => And.left (originalStageSingleMarking_relativeCartier K n h m i)
local notation "L" => originalStageSinglePointLine K n h m i

/-- Every retained tensor section obeys the original full Laurent overlap equation. -/
theorem completePointStageChartNumerator_laurent (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) :
    leftLaurentMap (t) (a j) ^ d *
      precedingLaurentMap (Ring K m) (t)
        (completePointStageChartNumerator K n h m i (p) d s) =
    precedingLaurentMap (Ring K m) (t) (a (p)) ^ d *
      leftLaurentMap (t) (completePointStageChartNumerator K n h m i j d s) := by
  have hq : Spec.map (CommRingCat.ofHom (leftLaurentMap (t)).toRingHom) ≫ (f j) =
      Spec.map (CommRingCat.ofHom (precedingLaurentMap (Ring K m) (t)).toRingHom) ≫
        (f (p)) := by
    rw [← leftBranchOpen_eq_spec, ← precedingBranch_eq_spec]
    exact PolygonInfinitesimal.overlap (Ring K m) (t) n h j
  have he := divisorAffineNumerator_overlap hI (f j) (f (p)) (g j) (g (p))
    (PolygonInfinitesimal.markingImageEquation_regular (Ring K m) (t) n h i j 1)
    (PolygonInfinitesimal.markingImageEquation_regular (Ring K m) (t) n h i (p) 1)
    (PolygonInfinitesimal.markingImageIdeal_equation (Ring K m) (t) n h i j 1)
    (PolygonInfinitesimal.markingImageIdeal_equation (Ring K m) (t) n h i (p) 1)
    (leftLaurentMap (t)).toRingHom (precedingLaurentMap (Ring K m) (t)).toRingHom hq d s
  have hg (k : Fin n) : coordinates (f k) (g k) = (a k) :=
    PolygonInfinitesimal.markingImageEquation_coordinate (Ring K m) (t) n h i k 1
  erw [hg j, hg (p)] at he
  rw [completePointStageChartNumerator_def, completePointStageChartNumerator_def]
  exact he

/-- The retained order-two numerators satisfy the same full cyclic compatibility. -/
theorem completePointStagePoleTwoChartNumerator_laurent :
    leftLaurentMap (t) (a j) ^ 2 * precedingLaurentMap (Ring K m) (t)
      (completePointStagePoleTwoChartNumerator K n h m i (p)) =
    precedingLaurentMap (Ring K m) (t) (a (p)) ^ 2 * leftLaurentMap (t)
      (completePointStagePoleTwoChartNumerator K n h m i j) :=
  completePointStageChartNumerator_laurent K n h m i j 2 _

/-- The retained order-three numerators satisfy compatibility with every lower term present. -/
theorem completePointStagePoleThreeChartNumerator_laurent :
    leftLaurentMap (t) (a j) ^ 3 * precedingLaurentMap (Ring K m) (t)
      (completePointStagePoleThreeChartNumerator K n h m i (p)) =
    precedingLaurentMap (Ring K m) (t) (a (p)) ^ 3 * leftLaurentMap (t)
      (completePointStagePoleThreeChartNumerator K n h m i j) :=
  completePointStageChartNumerator_laurent K n h m i j 3 _

end FLT.Mazur.PolygonInfinitesimalStages
