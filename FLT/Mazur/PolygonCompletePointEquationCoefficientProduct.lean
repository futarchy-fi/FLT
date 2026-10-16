/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineDivisorEquationPowerCoordinates
public import FLT.Mazur.ModuleComparedTensorSectionProduct
public import FLT.Mazur.PolygonCompletePointStageEquationFrames

/-!
# Products in the original polygon equation frames

The equation frames are coherent in their original tensor degrees. The
actual chart pullback and the original unit-one marking therefore carry
homogeneous products to products of their retained equation coefficients.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] ModuleSheafTensor.tensor divisorLineBundle
variable {X Y : Scheme} [IsAffine X] {L : Y.Modules} {I : X.IdealSheafData}

/-- A pulled line comparison followed by equation evaluation preserves original products. -/
theorem divisorPulledEquationFrame_product (f : X ⟶ Y) (hI : EffectiveCartier I)
    (e : (pullback f).obj L ≅ divisorLineBundle I hI)
    (a : Γ(X, ⊤)) (ha : IsRegular a)
    (he : I.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {a}) (d k : ℕ)
    (s : Γ(tensorPower L d, ⊤)) (v : Γ(tensorPower L k, ⊤)) :
    (tensorPowerPullbackComparison f e (d + k) ≪≫
      divisorEquationPowerFrame hI a ha he (d + k)).hom.app ⊤
        (pullGlobal f _ (SectionGradedMultiplication.mul L ⊤ d k s v)) =
      (show Γ(X, ⊤) from (tensorPowerPullbackComparison f e d ≪≫
        divisorEquationPowerFrame hI a ha he d).hom.app ⊤ (pullGlobal f _ s)) *
      (show Γ(X, ⊤) from (tensorPowerPullbackComparison f e k ≪≫
        divisorEquationPowerFrame hI a ha he k).hom.app ⊤ (pullGlobal f _ v)) := by
  simp only [sectionIso_trans]
  rw [tensorPowerPullbackComparison_product, divisorEquationPowerFrame_mul]

end FLT.Mazur.FCurve

namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing FCurve ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj ModuleSheafTensor.tensor divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i : Fin n)
local notation "t" => parameter K m
local notation "f" => PolygonInfinitesimal.chart (Ring K m) (t) n h i
local notation "q" => markedSection (t) (1 : (Ring K m)ˣ)
local notation "L" => originalStageSinglePointLine K n h m i

/-- The actual chart-frame coordinates multiply in the original tensor degrees. -/
theorem completePointStageChartEquationFrame_product (d k : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) (v : Γ(tensorPower (L) k, ⊤)) :
    (completePointStageChartEquationFrame K n h m i (d + k)).hom.app ⊤
      (pullGlobal (f) _ (SectionGradedMultiplication.mul (L) ⊤ d k s v)) =
      (show Γ(Spec (.of (ChartRing (t))), ⊤) from
        (completePointStageChartEquationFrame K n h m i d).hom.app ⊤ (pullGlobal (f) _ s)) *
      (show Γ(Spec (.of (ChartRing (t))), ⊤) from
        (completePointStageChartEquationFrame K n h m i k).hom.app ⊤ (pullGlobal (f) _ v)) := by
  let _ : IsAffine (PolygonSmoothing.chart (Ring K m) (t)) :=
    inferInstanceAs (IsAffine (Spec (.of (ChartRing (t)))))
  simp only [completePointStageChartEquationFrame_def]
  exact divisorPulledEquationFrame_product (f) _ _ _ _ _ d k s v

/-- The original marking coefficient respects multiplication over the full stage ring. -/
theorem completePointStageEquationCoefficient_product (d k : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) (v : Γ(tensorPower (L) k, ⊤)) :
    completePointStageEquationCoefficient K n h m i (d + k)
      (SectionGradedMultiplication.mul (L) ⊤ d k s v) =
        completePointStageEquationCoefficient K n h m i d s *
          completePointStageEquationCoefficient K n h m i k v := by
  simp only [completePointStageEquationCoefficient_chart]
  rw [completePointStageChartEquationFrame_product, map_mul]

end FLT.Mazur.PolygonInfinitesimalStages
