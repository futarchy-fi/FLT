/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticOriginalSectionReconstruction
public import FLT.Mazur.ComparedStageSectionReconstruction
public import FLT.Mazur.PolygonArithmeticLineOriginalReduction

/-!
# Reconstruction through specified original-stage line comparisons

A coherent comparison with original stage modules transports proper formal
section reconstruction. The resulting complete section has the specified
original images, rather than images under newly chosen quotient identifications.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonArithmeticStages

open FCurve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] originalStageToCompatibleProj family

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : (exactVeroneseProj A π n h hne hgen).Modules) (hL : LocallyFreeRankOne L)

include hL

/-- Coherent original stage comparisons transport unique complete section reconstruction. -/
theorem completeLineComparedSection_existsUnique
    (M : ∀ m, (family A π m n h).left.Modules)
    (e : ∀ m, completeLineOnStage A π hne hgen n h L m ≅ M m)
    (d : ∀ {a b : ℕ}, (f : a ⟶ b) →
      (pullback ((stageSystem A π n h).map f)).obj (M b) ⟶ M a)
    (he : ∀ {a b : ℕ} (f : a ⟶ b),
      (pullback ((stageSystem A π n h).map f)).map (e b).hom ≫ d f =
        (completeLineStageTransitionIso A π hne hgen n h L f).hom ≫ (e a).hom)
    (s : ∀ m, Γ(M m, ⊤))
    (hs : ∀ a b (hab : a ≤ b),
      (d (homOfLE hab)).app ⊤
        (pullGlobal ((stageSystem A π n h).map (homOfLE hab)) (M b) (s b)) = s a) :
    ∃! t : Γ(L, ⊤), ∀ m,
      (e m).hom.app ⊤
        (pullGlobal (originalStageToCompatibleProj A π hne hgen n h m) L t) = s m := by
  apply sectionReconstruction_of_stageComparison L (fun m ↦ (family A π m n h).left)
    (originalStageToCompatibleProj A π hne hgen n h)
    (fun {_ _} hab ↦ (stageSystem A π n h).map (homOfLE hab))
    (fun _ _ hab ↦ originalStageToCompatibleProj_naturality A π hne hgen n h (homOfLE hab))
    M e (fun {_ _} hab ↦ d (homOfLE hab))
    (fun {_ _} hab ↦ ?_) (completeLineOriginalSection_existsUnique A π hne hgen n h L hL) s hs
  rw [← completeLineStageTransitionIso_eq_sealed]
  exact he (homOfLE hab)

end FLT.Mazur.PolygonArithmeticStages
