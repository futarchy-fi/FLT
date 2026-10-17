/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartesianActionPullback
public import FLT.Mazur.PolygonCompleteClosedWholeAction

/-!
# Equivariance of the actual closed polygon pullback

The original split group and polygon identify with the literal closed fibers
of the full smooth group and whole curve, compatibly with their entire actions.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "C" => PolygonCyclicAtlas.polygon K n h
local notation "G" => PolygonSplitGroup.model K n
local notation "M" => completeOriginalSmoothOver K n h
local notation "X" => completeOriginalWholeOver K n h
local notation "b" => completeClosedBase K
local notation "P" => PolygonCyclicAtlas.normalization K n h
local notation "Q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn

/-- The original closed polygon is the literal pullback of the whole family. -/
def completeClosedWholePullbackIso : (C) ≅ (Over.pullback (b)).obj (X) :=
  CartesianActionPullback.comparison (b) (completeClosedFiberInclusion K n h)
    (completeClosedFiber_isPullback K n h)

/-- The original split smooth group is the literal pullback of the full smooth group. -/
def completeClosedGroupPullbackIso : (G) ≅ (Over.pullback (b)).obj (M) :=
  CartesianActionPullback.comparison (b) (completeClosedSplitInclusion K n h)
    (completeClosedSplitInclusion_isPullback K n h)

/-- The whole comparison retains the original closed-family embedding. -/
@[reassoc] theorem completeClosedWholePullbackIso_fst :
    (completeClosedWholePullbackIso K n h).hom.left ≫ pullback.fst (X).hom (b) =
      completeClosedFiberInclusion K n h :=
  CartesianActionPullback.comparison_fst _ _ _

/-- The group comparison retains the original full split-parameter embedding. -/
@[reassoc] theorem completeClosedGroupPullbackIso_fst :
    (completeClosedGroupPullbackIso K n h).hom.left ≫ pullback.fst (M).hom (b) =
      completeClosedSplitInclusion K n h :=
  CartesianActionPullback.comparison_fst _ _ _

/-- The actual closed pullback comparisons intertwine the whole polygon actions. -/
theorem completeClosedPullback_action :
    PolygonUniversalAction.act K n hn P Q hp ≫
      (completeClosedWholePullbackIso K n h).hom =
    ((completeClosedGroupPullbackIso K n h).hom ⊗ₘ
      (completeClosedWholePullbackIso K n h).hom) ≫
      Functor.LaxMonoidal.μ (Over.pullback (b)) (M) (X) ≫
        (Over.pullback (b)).map (completeWholeAction K n h) :=
  CartesianActionPullback.action_comparison (b) _ _
    (completeClosedSplitInclusion_isPullback K n h)
    (completeClosedFiber_isPullback K n h) (completeClosedActionInput K n h)
    (completeClosedActionInput_fst K n h) (completeClosedActionInput_snd K n h)
    (completeWholeAction K n h) (PolygonUniversalAction.act K n hn P Q hp)
    (completeWholeAction_closed K n h).symm

end FLT.Mazur.PolygonInfinitesimalStages
