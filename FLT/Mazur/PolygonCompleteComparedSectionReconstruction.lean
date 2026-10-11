/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteOriginalSectionReconstruction
public import FLT.Mazur.ComparedStageSectionReconstruction

/-!
# Reconstruction through specified original-stage line comparisons

A coherent comparison with original stage modules transports proper formal
section reconstruction. The resulting complete section has the specified
original images, rather than images under newly chosen quotient identifications.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] originalStageToCompatibleProj family

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : (exactVeroneseProj K n h).Modules) (hL : LocallyFreeRankOne L)

include hL

/-- Coherent original stage comparisons transport unique complete section reconstruction. -/
theorem completeLineComparedSection_existsUnique
    (M : ∀ m, (family K m n h).left.Modules)
    (e : ∀ m, completeLineOnStage K n h L m ≅ M m)
    (d : ∀ {a b : ℕ}, (f : a ⟶ b) →
      (pullback ((stageSystem K n h).map f)).obj (M b) ⟶ M a)
    (he : ∀ {a b : ℕ} (f : a ⟶ b),
      (pullback ((stageSystem K n h).map f)).map (e b).hom ≫ d f =
        (completeLineStageTransitionIso K n h L f).hom ≫ (e a).hom)
    (s : ∀ m, Γ(M m, ⊤))
    (hs : ∀ a b (hab : a ≤ b),
      (d (homOfLE hab)).app ⊤
        (pullGlobal ((stageSystem K n h).map (homOfLE hab)) (M b) (s b)) = s a) :
    ∃! t : Γ(L, ⊤), ∀ m,
      (e m).hom.app ⊤ (pullGlobal (originalStageToCompatibleProj K n h m) L t) = s m := by
  apply sectionReconstruction_of_stageComparison L (fun m ↦ (family K m n h).left)
    (originalStageToCompatibleProj K n h)
    (fun {_ _} hab ↦ (stageSystem K n h).map (homOfLE hab))
    (fun _ _ hab ↦ originalStageToCompatibleProj_naturality K n h (homOfLE hab))
    M e (fun {_ _} hab ↦ d (homOfLE hab))
    (fun {_ _} hab ↦ ?_) (completeLineOriginalSection_existsUnique K n h L hL) s hs
  rw [← completeLineStageTransitionIso_eq_sealed]
  exact he (homOfLE hab)

end FLT.Mazur.PolygonInfinitesimalStages
