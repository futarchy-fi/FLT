/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.LineMorphismSectionStage
public import FLT.Mazur.PolygonArithmeticLineHomExt
public import FLT.Mazur.PolygonArithmeticComparedSectionReconstruction

/-!
# Reconstructing morphisms between complete lines from original stages

Compatible morphisms yield compatible sections of the actual tensor-dual
line. Proper formal section reconstruction then gives a unique global
morphism with the specified original-stage restrictions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonArithmeticStages
open FCurve ModuleSheafTensor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] originalStageToCompatibleProj exactVeroneseProj family tensor
  lineMorphismTensorPullbackIso
variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {L M : (exactVeroneseProj A π n h hne hgen).Modules}
  (hL : LocallyFreeRankOne L) (hM : LocallyFreeRankOne M)

include hL hM

/-- Compatible actual stage morphisms reconstruct a unique complete line morphism. -/
theorem completeLineHom_existsUnique
    (a : ∀ m, (pullback (originalStageToCompatibleProj A π hne hgen n h m)).obj L ⟶
      (pullback (originalStageToCompatibleProj A π hne hgen n h m)).obj M)
    (ha : ∀ {i j : ℕ} (f : i ⟶ j),
      (pullback ((stageSystem A π n h).map f)).map (a j) ≫
          (completeLineStageTransitionIso A π hne hgen n h M f).hom =
        (completeLineStageTransitionIso A π hne hgen n h L f).hom ≫ a i) :
    ∃! b : L ⟶ M, ∀ m,
      (pullback (originalStageToCompatibleProj A π hne hgen n h m)).map b = a m := by
  let p := originalStageToCompatibleProj A π hne hgen n h
  let N := fun m ↦ tensor ((pullback (p m)).obj M) (moduleSheafDual ((pullback (p m)).obj L))
  let e := fun m ↦ lineMorphismTensorPullbackIso hL M (p m)
  let d := fun {i j : ℕ} (f : i ⟶ j) ↦ lineMorphismSectionTransition (p i) (p j)
    ((stageSystem A π n h).map f) (originalStageToCompatibleProj_naturality A π hne hgen n h f) hL M
  let s := fun m ↦ lineMorphismSectionEquiv (hL.pullback (p m)) _ (a m)
  have he {i j : ℕ} (f : i ⟶ j) :
      (pullback ((stageSystem A π n h).map f)).map (e j).hom ≫ d f =
        (completeLineStageTransitionIso A π hne hgen n h (tensor M (moduleSheafDual L)) f).hom ≫
          (e i).hom := by
    rw [completeLineStageTransitionIso_eq_sealed]
    exact lineMorphismTensorPullbackIso_stage (p i) (p j) _ _ hL M
  have hs (i j : ℕ) (hij : i ≤ j) :
      (d (homOfLE hij)).app ⊤
        (pullGlobal ((stageSystem A π n h).map (homOfLE hij)) (N j) (s j)) = s i := by
    apply lineMorphismSectionTransition_apply
    simpa only [completeLineStageTransitionIso_eq_sealed] using ha (homOfLE hij)
  obtain ⟨t, ht, _⟩ := completeLineComparedSection_existsUnique A π hne hgen n h
    (tensor M (moduleSheafDual L)) (hM.tensor hL.dual) N e d (fun f ↦ he f) s hs
  refine ⟨(lineMorphismSectionEquiv hL M).symm t, ?_, ?_⟩
  · intro m
    apply (lineMorphismSectionEquiv (hL.pullback (p m)) _).injective
    rw [← lineMorphismSectionEquiv_pullback, Equiv.apply_symm_apply]
    exact ht m
  · intro b hb
    apply completeLineHom_ext_stages A π hne hgen n h hL hM
    intro m
    rw [hb]
    apply (lineMorphismSectionEquiv (hL.pullback (p m)) _).injective
    rw [← lineMorphismSectionEquiv_pullback, Equiv.apply_symm_apply]
    exact (ht m).symm

end FLT.Mazur.PolygonArithmeticStages
