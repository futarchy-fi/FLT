/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticStageProjectiveCoordinates
public import FLT.Mazur.SectionCubicEquationPullback

/-!
# Cubic morphisms from original arithmetic stage coordinates

The normalized equations for a specified cubic construct the finite-stage
maps. Their projective compatibility and transition compatibility follow
from actual section reconstruction, without supplied finite-stage maps.
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

/-- The coefficient map of the original finite family over the integral base. -/
def originalIntegralStageScalars (m : ℕ) : A →+* Γ((family A π m n h).left, ⊤) :=
  ((family A π m n h).hom ≫ baseToIntegral A π m).appTop.hom.comp
    (Scheme.ΓSpecIso (.of A)).inv.hom

local notation "Lₛ" => completeLineOnStage A π hne hgen n h L
local notation "rₛ" => originalIntegralStageScalars A π n h
local notation "cₛ" => completeOriginalStageSections_cover A π hne hgen n h L hL 2 s hs hcover
variable (W : WeierstrassCurve A)
  (he : ∀ m, CubicCoordinateEquations (completeLineOnStage A π hne hgen n h L m)
    W (fun i ↦ s i m) (originalIntegralStageScalars A π n h m))

/-- The specified normalized equations construct an actual original-stage cubic morphism. -/
def completeOriginalStageCubicMap (m : ℕ) : (family A π m n h).left ⟶ integralCurve W :=
  coordinateCubicMorphism (Lₛ m) W (fun i ↦ s i m) (cₛ m) (rₛ m) (he m)

/-- The finite cubic map has exactly the restriction of the reconstructed projective map. -/
@[reassoc] theorem completeOriginalStageCubicMap_projective (m : ℕ) :
    completeOriginalStageCubicMap A π hne hgen n h L hL s hs hcover W he m ≫
        integralProjectiveMap W =
      originalStageToCompatibleProj A π hne hgen n h m ≫
        completeOriginalProjectiveMap A π hne hgen n h L hL 2 s hs hcover := by
  rw [completeOriginalStageCubicMap, coordinateCubicMorphism_projective,
    completeOriginalProjectiveMap_stage, originalIntegralStageScalars]

/-- The constructed finite maps preserve every original arithmetic stage transition. -/
@[reassoc] theorem completeOriginalStageCubicMap_transition {a b : ℕ} (f : a ⟶ b) :
    (stageSystem A π n h).map f ≫
        completeOriginalStageCubicMap A π hne hgen n h L hL s hs hcover W he b =
      completeOriginalStageCubicMap A π hne hgen n h L hL s hs hcover W he a := by
  apply (cancel_mono (integralProjectiveMap W)).mp
  rw [Category.assoc, completeOriginalStageCubicMap_projective,
    completeOriginalStageCubicMap_projective, ← Category.assoc,
    originalStageToCompatibleProj_naturality]

/-- The finite cubic morphism lies over the original coefficient ring map. -/
@[reassoc] theorem completeOriginalStageCubicMap_toBase (m : ℕ) :
    completeOriginalStageCubicMap A π hne hgen n h L hL s hs hcover W he m ≫
        integralCurveStructure W = (family A π m n h).hom ≫ baseToIntegral A π m := by
  rw [← integralProjectiveMap_baseProjection, ← Category.assoc,
    completeOriginalStageCubicMap_projective, Category.assoc,
    completeOriginalProjectiveMap_toBase, originalStageToCompatibleProj_toBase]

end FLT.Mazur.PolygonArithmeticStages
