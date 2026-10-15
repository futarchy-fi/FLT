/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticSectionLift
public import FLT.Mazur.ModuleSectionProjectiveOver

/-!
# Algebraizing arithmetic projective coordinates

Compatible original-stage coordinates in a complete line, generating on the
closed stage, define an actual global projective morphism over the original
coefficient ring. Every chart retains its original generator open at every order.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonArithmeticStages
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] originalStageToCompatibleProj family
  exactVeroneseProj exactVeroneseProjToBase
variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : (exactVeroneseProj A π n h hne hgen).Modules) (hL : LocallyFreeRankOne L)
  (d : ℕ) (s : Fin (d + 1) → ∀ m, Γ(completeLineOnStage A π hne hgen n h L m, ⊤))
  (hs : ∀ i a b (hab : a ≤ b),
    (completeLineStageTransitionIso A π hne hgen n h L (homOfLE hab)).hom.app ⊤
      (pullGlobal ((stageSystem A π n h).map (homOfLE hab)) _ (s i b)) = s i a)
  (hcover : (⨆ i, sectionGeneratorOpen
    (completeLineOnStage A π hne hgen n h L 0) (s i 0)) = ⊤)

/-- Algebraized original coordinates give a genuine morphism over the arithmetic coefficients. -/
def completeOriginalProjectiveMap :
    exactVeroneseProj A π n h hne hgen ⟶ ProjectiveSpace.space A (Fin (d + 1)) :=
  sectionProjectiveMorphism L d
    (fun i ↦ completeOriginalSectionLift A π hne hgen n h L hL (s i) (hs i))
    (completeOriginalSectionLift_cover A π hne hgen n h L hL s hs hcover)
    ((exactVeroneseProjToBase A π n h hne hgen).appTop.hom.comp
      (Scheme.ΓSpecIso (.of A)).inv.hom)

/-- The reconstructed map preserves the original integral structural morphism. -/
@[reassoc] theorem completeOriginalProjectiveMap_toBase :
    completeOriginalProjectiveMap A π hne hgen n h L hL d s hs hcover ≫
      ProjectiveSpace.baseProjection A (Fin (d + 1)) =
        exactVeroneseProjToBase A π n h hne hgen :=
  sectionProjectiveMorphism_baseProjection L d _ _ _

/-- Every original-stage chart is exactly the original coordinate generator open. -/
theorem completeOriginalProjectiveMap_stage_chart (m : ℕ) (i : Fin (d + 1)) :
    (originalStageToCompatibleProj A π hne hgen n h m ≫
      completeOriginalProjectiveMap A π hne hgen n h L hL d s hs hcover) ⁻¹ᵁ
        ProjectiveSpace.chart A (Fin (d + 1)) i =
      sectionGeneratorOpen (completeLineOnStage A π hne hgen n h L m) (s i m) := by
  rw [Scheme.Hom.comp_preimage, completeOriginalProjectiveMap,
    sectionProjectiveMorphism_preimage_chart, completeOriginalSectionLift_generatorOpen]

end FLT.Mazur.PolygonArithmeticStages
