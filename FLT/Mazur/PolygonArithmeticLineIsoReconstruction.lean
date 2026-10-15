/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticLineHomReconstruction
public import FLT.Mazur.PolygonArithmeticLineIsoDetection

/-!
# Reconstructing original compatible complete-line isomorphisms

Formal reconstruction supplies the actual morphism. Its original closed
restriction is invertible, so properness proves global invertibility.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonArithmeticStages
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] originalStageToCompatibleProj exactVeroneseProj family
variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Compatible original line isomorphisms reconstruct uniquely on the complete family. -/
theorem completeLineIso_existsUnique {L M : (exactVeroneseProj A π n h hne hgen).Modules}
    (hL : LocallyFreeRankOne L) (hM : LocallyFreeRankOne M)
    (a : ∀ m, (pullback (originalStageToCompatibleProj A π hne hgen n h m)).obj L ≅
      (pullback (originalStageToCompatibleProj A π hne hgen n h m)).obj M)
    (ha : ∀ {i j : ℕ} (f : i ⟶ j),
      (pullback ((stageSystem A π n h).map f)).map (a j).hom ≫
          (completeLineStageTransitionIso A π hne hgen n h M f).hom =
        (completeLineStageTransitionIso A π hne hgen n h L f).hom ≫ (a i).hom) :
    ∃! b : L ≅ M, ∀ m,
      (pullback (originalStageToCompatibleProj A π hne hgen n h m)).mapIso b = a m := by
  obtain ⟨b, hb, _⟩ := completeLineHom_existsUnique A π hne hgen n h hL hM (fun m ↦ (a m).hom) ha
  have : IsIso ((pullback (originalStageToCompatibleProj A π hne hgen n h 0)).map b) := by
    rw [hb]
    infer_instance
  let _ := completeLineHom_isIso_of_originalZero A π hne hgen n h hL hM b
  refine ⟨asIso b, fun m ↦ Iso.ext (hb m), ?_⟩
  intro c hc
  apply completeLineIso_ext_stages A π hne hgen n h hL hM
  intro m
  exact (hc m).trans (Iso.ext (hb m)).symm

end FLT.Mazur.PolygonArithmeticStages
