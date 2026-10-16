/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorAffineLocalizedNumerator
public import FLT.Mazur.PolygonCompletePointStageBoundedNumerators
public import FLT.Mazur.PolygonCompletePointNodeLocalization

/-!
# Original pole numerators on the whole marking complement

The numerator identities hold under every original chart map factoring
through the actual marking complement. Inverting the two-coordinate node
denominator is unnecessary, and arbitrary receiving-ring nilpotents remain.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing FCurve AffineImmersionSectionCoordinates
open ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj ModuleSheafTensor.tensor divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i j : Fin n)
local notation "f" => PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h j
local notation "C" => GlobalIdealPowerCompatibility.complement
  (Scheme.Hom.ker (marking K m n h i))
local notation "hI" => And.left (originalStageSingleMarking_relativeCartier K n h m i)
local notation "L" => originalStageSinglePointLine K n h m i
variable {B : Type} [CommRing B]
variable (σ : ChartRing (parameter K m) →+* B)
variable (v : Spec (.of B) ⟶ (completePointStageNodeOpen K n h m i j).toScheme)
variable (hv : v ≫ (completePointStageNodeOpen K n h m i j).ι =
  Spec.map (CommRingCat.ofHom σ))

/-- Pull back the retained complement functions along an arbitrary original chart map. -/
def completePointNodeComplementFunctions :
    Γ((completePointStageNodeOpen K n h m i j).toScheme, ⊤) →+* B :=
  (Scheme.ΓSpecIso (.of B)).hom.hom.comp v.appTop.hom
local notation "ψ" => completePointNodeComplementFunctions K n h m i j v
local notation "g" => PolygonInfinitesimal.markingImageEquation
  (Ring K m) (parameter K m) n h i j 1
local notation "a" => PolygonInfinitesimal.chartMarkingEquation
  (Ring K m) (parameter K m) n i j 1

include hv

/-- The original degree bounds the denominator of the very same node-localized section. -/
theorem completePointNodeComplementNumerator (d : ℕ) (hd : 0 < d)
    (s : Γ(tensorPower (L) d, ⊤)) :
    (σ) (a) ^ d * (ψ)
      (completePointStageNodeFunction K n h m i j d s) =
      (σ) (completePointStageChartNumerator K n h m i j d s) := by
  let q := v ≫ ((f) ∣_ (C))
  have hq : Spec.map (CommRingCat.ofHom σ) ≫ (f) = q ≫ (C).ι := by
    dsimp only [q]
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc]
    exact congrArg (fun z ↦ z ≫ (f))
      hv.symm
  have he := divisorAffineLocalizedNumerator hI (f) (g)
    (PolygonInfinitesimal.markingImageEquation_regular (Ring K m) (parameter K m) n h i j 1)
    (PolygonInfinitesimal.markingImageIdeal_equation (Ring K m) (parameter K m) n h i j 1)
    (σ) q hq d hd s
  have hg : coordinates (f) (g) = (a) :=
    PolygonInfinitesimal.markingImageEquation_coordinate (Ring K m)
      (parameter K m) n h i j 1
  erw [hg] at he
  rw [completePointStageChartNumerator_def]
  exact he

/-- The square of the specified marking equation clears the retained order-two function. -/
theorem completePointNodeComplementPoleTwo_bounded :
    (σ) (a) ^ 2 * (ψ) (completePointStageNodePoleTwo K n h m i j) =
      (σ) (completePointStagePoleTwoChartNumerator K n h m i j) :=
  completePointNodeComplementNumerator K n h m i j σ v hv 2 (by decide) _

/-- The cube of that same equation clears the retained order-three function. -/
theorem completePointNodeComplementPoleThree_bounded :
    (σ) (a) ^ 3 * (ψ) (completePointStageNodePoleThree K n h m i j) =
      (σ) (completePointStagePoleThreeChartNumerator K n h m i j) :=
  completePointNodeComplementNumerator K n h m i j σ v hv 3 (by decide) _

end FLT.Mazur.PolygonInfinitesimalStages
