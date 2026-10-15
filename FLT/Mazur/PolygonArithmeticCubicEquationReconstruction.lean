/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticStageCubicCoordinates
public import FLT.Mazur.PolygonArithmeticWeierstrassReconstruction
public import FLT.Mazur.WeierstrassIntegralSeparated

/-!
# Algebraizing the original finite cubic coordinate equations

The actual finite maps and their projective compatibility are constructed
from the normalized equations. Closed-target reconstruction then produces
the complete cubic map over the original coefficient ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonArithmeticStages
open FCurve WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] originalStageToCompatibleProj family
  exactVeroneseProj exactVeroneseProjToBase completeOriginalSectionLift
variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : (exactVeroneseProj A π n h hne hgen).Modules) (hL : LocallyFreeRankOne L)
  (s : Fin 3 → ∀ m, Γ(completeLineOnStage A π hne hgen n h L m, ⊤))
  (hs : ∀ i a b (hab : a ≤ b),
    (completeLineStageTransitionIso A π hne hgen n h L (homOfLE hab)).hom.app ⊤
      (pullGlobal ((stageSystem A π n h).map (homOfLE hab)) _ (s i b)) = s i a)
  (hcover : (⨆ i, sectionGeneratorOpen
    (completeLineOnStage A π hne hgen n h L 0) (s i 0)) = ⊤)

variable (W : WeierstrassCurve A)
  (he : ∀ m, CubicCoordinateEquations (completeLineOnStage A π hne hgen n h L m)
    W (fun i ↦ s i m) (originalIntegralStageScalars A π n h m))

/-- Original finite-order coordinate equations construct the complete cubic morphism. -/
def completeOriginalCubicMap : exactVeroneseProj A π n h hne hgen ⟶ integralCurve W :=
  completeWeierstrassMap A π hne hgen n h L hL s hs hcover W
    (completeOriginalStageCubicMap A π hne hgen n h L hL s hs hcover W he)
    (completeOriginalStageCubicMap_projective A π hne hgen n h L hL s hs hcover W he)

/-- The constructed complete map retains the prescribed projective coordinates. -/
@[reassoc] theorem completeOriginalCubicMap_projective :
    completeOriginalCubicMap A π hne hgen n h L hL s hs hcover W he ≫
        integralProjectiveMap W =
      completeOriginalProjectiveMap A π hne hgen n h L hL 2 s hs hcover :=
  completeWeierstrassMap_projective A π hne hgen n h L hL s hs hcover W _ _

/-- Every original stage is exactly its constructed normalized-coordinate cubic map. -/
@[reassoc] theorem completeOriginalCubicMap_stage (m : ℕ) :
    originalStageToCompatibleProj A π hne hgen n h m ≫
        completeOriginalCubicMap A π hne hgen n h L hL s hs hcover W he =
      completeOriginalStageCubicMap A π hne hgen n h L hL s hs hcover W he m :=
  completeWeierstrassMap_stage A π hne hgen n h L hL s hs hcover W _ _ m

/-- Reconstruction preserves the specified original integral coefficient morphism. -/
@[reassoc] theorem completeOriginalCubicMap_toBase :
    completeOriginalCubicMap A π hne hgen n h L hL s hs hcover W he ≫
        integralCurveStructure W = exactVeroneseProjToBase A π n h hne hgen :=
  completeWeierstrassMap_toBase A π hne hgen n h L hL s hs hcover W _ _

/-- No other complete morphism has these original finite-order coordinate maps. -/
theorem completeOriginalCubicMap_unique (k : exactVeroneseProj A π n h hne hgen ⟶
    integralCurve W)
    (hk : ∀ m, originalStageToCompatibleProj A π hne hgen n h m ≫ k =
      completeOriginalStageCubicMap A π hne hgen n h L hL s hs hcover W he m) :
    k = completeOriginalCubicMap A π hne hgen n h L hL s hs hcover W he := by
  let _ : (integralCurve W).IsSeparated :=
    (HasAffineProperty.iff_of_isAffine (P := @IsSeparated)).mp
      (integralCurveStructure_separated W)
  apply completeFamilyHom_ext_stages A π hne hgen n h
  intro m
  rw [hk, completeOriginalCubicMap_stage]

/-- Identified original stage markings give the actual complete marking. -/
@[reassoc] theorem completeOriginalCubicMap_marking (i : Fin n)
    (t : Spec (.of A) ⟶ integralCurve W)
    (ht : ∀ m, marking A π m n h i ≫
      completeOriginalStageCubicMap A π hne hgen n h L hL s hs hcover W he m =
        baseToIntegral A π m ≫ t) :
    completeBaseMarking A π hne hgen n h i ≫
      completeOriginalCubicMap A π hne hgen n h L hL s hs hcover W he = t :=
  completeWeierstrassMap_marking A π hne hgen n h L hL s hs hcover W _ _ i t ht

end FLT.Mazur.PolygonArithmeticStages
