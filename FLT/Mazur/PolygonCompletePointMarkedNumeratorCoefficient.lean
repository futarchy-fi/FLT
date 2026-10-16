/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointChartFrameNumerator
public import FLT.Mazur.PolygonCompletePointStageFrameUnits

/-!
# Laurent evaluation of the original equation-frame coefficient

At every full stage, evaluating the retained outgoing numerator at the
unit-one marking is exactly its coefficient in the equation frame.
The retained quadratic and cubic lifts thus have their actual comparison
units as marking values, without replacing or normalizing either lift.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing FCurve ModuleLineBundleTensorPullback LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj ModuleSheafTensor.tensor divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i : Fin n)
local notation "t" => parameter K m
local notation "L" => originalStageSinglePointLine K n h m i
local notation "N" => completePointStageChartNumerator K n h m i i

/-- The original chart numerator evaluates to the actual equation-frame coefficient. -/
theorem completePointStageEquationCoefficient_marked (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) :
    (Scheme.ΓSpecIso (.of (Ring K m))).hom
      (completePointStageEquationCoefficient K n h m i d s) =
        markedEvaluation (t) 1 (N d s) := by
  rw [completePointStageEquationCoefficient_chart]
  have hn := Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom (markedEvaluation (t) 1).toRingHom)
  have he := congrArg (fun k ↦ k.hom
    ((completePointStageChartEquationFrame K n h m i d).hom.app ⊤
      (pullGlobal (PolygonInfinitesimal.chart (Ring K m) (t) n h i) _ s))) hn
  change _ = markedEvaluation (t) 1
    ((Scheme.ΓSpecIso (.of (ChartRing (t)))).hom
      ((completePointStageChartEquationFrame K n h m i d).hom.app ⊤
        (pullGlobal (PolygonInfinitesimal.chart (Ring K m) (t) n h i) _ s))) at he
  rw [completePointStageChartEquationFrame_numerator] at he
  exact he

/-- The original outgoing Laurent value at one is the same equation coefficient. -/
theorem completePointStageNumerator_eval_one (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) :
    eval₂ (RingHom.id (Ring K m)) 1 (leftLaurentMap (t) (N d s)) =
      (Scheme.ΓSpecIso (.of (Ring K m))).hom
        (completePointStageEquationCoefficient K n h m i d s) := by
  rw [completePointStageEquationCoefficient_marked]
  exact DFunLike.congr_fun (markedEvaluation_laurent (t) 1) (N d s)

/-- The same frame comparison unit in the original arithmetic stage ring. -/
def completePointStageArithmeticFrameUnit (d : ℕ) : (Ring K m)ˣ :=
  Units.map (Scheme.ΓSpecIso (.of (Ring K m))).hom.hom.toMonoidHom
    (completePointStageFrameUnit K n h m i d)

/-- The quadratic marking value is the exact retained comparison unit in degree two. -/
theorem completePointStagePoleTwoNumerator_eval_one :
    eval₂ (RingHom.id (Ring K m)) 1 (leftLaurentMap (t)
      (completePointStagePoleTwoChartNumerator K n h m i i)) =
        (completePointStageArithmeticFrameUnit K n h m i 2 : Ring K m) := by
  rw [completePointStagePoleTwoChartNumerator, completePointStageNumerator_eval_one,
    completePointStagePoleTwo_equationCoefficient]
  rfl

/-- The cubic marking value keeps its own exact degree-three comparison unit. -/
theorem completePointStagePoleThreeNumerator_eval_one :
    eval₂ (RingHom.id (Ring K m)) 1 (leftLaurentMap (t)
      (completePointStagePoleThreeChartNumerator K n h m i i)) =
        (completePointStageArithmeticFrameUnit K n h m i 3 : Ring K m) := by
  rw [completePointStagePoleThreeChartNumerator, completePointStageNumerator_eval_one,
    completePointStagePoleThree_equationCoefficient]
  rfl

/-- The actual quadratic numerator's full-stage marking value is a unit. -/
theorem completePointStagePoleTwoNumerator_eval_one_isUnit :
    IsUnit (eval₂ (RingHom.id (Ring K m)) 1 (leftLaurentMap (t)
      (completePointStagePoleTwoChartNumerator K n h m i i))) := by
  rw [completePointStagePoleTwoChartNumerator, completePointStageNumerator_eval_one]
  exact (completePointStagePoleTwo_equationCoefficient_isUnit K n h m i).map
    (Scheme.ΓSpecIso (.of (Ring K m))).hom.hom

/-- The original cubic numerator has its own unit marking value over the full stage ring. -/
theorem completePointStagePoleThreeNumerator_eval_one_isUnit :
    IsUnit (eval₂ (RingHom.id (Ring K m)) 1 (leftLaurentMap (t)
      (completePointStagePoleThreeChartNumerator K n h m i i))) := by
  rw [completePointStagePoleThreeChartNumerator, completePointStageNumerator_eval_one]
  exact (completePointStagePoleThree_equationCoefficient_isUnit K n h m i).map
    (Scheme.ΓSpecIso (.of (Ring K m))).hom.hom

end FLT.Mazur.PolygonInfinitesimalStages
