/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedParameterReduction

/-!
# The original split smooth parameter is the complete smooth closed fiber

The existing smooth-locus isomorphism gives the actual full closed parameter
inclusion. Its Cartesian square and all original Laurent components are retained.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "C" => PolygonCyclicAtlas.polygon K n h
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn
local notation "G" => PolygonSplitGroup.model K n
local notation "M" => completeOriginalSmoothOver K n h
attribute [local instance] completeClosedPolygon_lfp exactVeroneseProjToBase_lfp
  PolygonPinching.cyclic_lfp
local notation "e" => smoothIso K n hn p q hp

/-- The full old split parameter enters the actual original relative smooth scheme. -/
def completeClosedSplitInclusion : (G).left ⟶ (M).left :=
  (e).inv.left ≫ completeClosedSmoothInclusion K n h

/-- The original split parameter retains the actual residue-field structure map. -/
@[reassoc] theorem completeClosedSplitInclusion_base :
    completeClosedSplitInclusion K n h ≫ (M).hom = (G).hom ≫ completeClosedBase K := by
  change (e).inv.left ≫ completeClosedSmoothInclusion K n h ≫
    (exactVeroneseProjToBase K n h).smoothLocus.ι ≫ exactVeroneseProjToBase K n h = _
  rw [completeClosedSmoothInclusion_structure]
  have hw := (e).inv.w
  change (e).inv.left ≫ ((PolygonCyclicAtlas.toBase K n h).smoothLocus.ι ≫
    PolygonCyclicAtlas.toBase K n h) = (G).hom at hw
  simpa only [Category.assoc] using congrArg (· ≫ completeClosedBase K) hw

/-- The full split smooth parameter is the actual Cartesian closed fiber. -/
theorem completeClosedSplitInclusion_isPullback :
    IsPullback (completeClosedSplitInclusion K n h) (G).hom (M).hom
      (completeClosedBase K) := by
  have hs : IsPullback (e).inv.left (G).hom
      ((PolygonCyclicAtlas.toBase K n h).smoothLocus.ι ≫ PolygonCyclicAtlas.toBase K n h)
      (𝟙 (Spec (.of K))) := IsPullback.of_horiz_isIso ⟨by
        rw [Category.comp_id]
        exact (e).inv.w⟩
  have ht := hs.paste_horiz (completeClosedSmoothInclusion_isPullback K n h)
  rw [Category.id_comp] at ht
  exact ht

/-- Each old split component is exactly the original closed finite Laurent chart. -/
@[reassoc] theorem component_completeClosedSplitInclusion (i : Fin n) :
    (PolygonSplitGroup.component K n (ZMod.finEquiv n i)).left ≫
        completeClosedSplitInclusion K n h =
      completeClosedFiniteChart K n h i ≫ completeClosedSmoothInclusion K n h := by
  have he : (PolygonSplitGroup.component K n (ZMod.finEquiv n i)).left ≫
      (e).inv.left = completeClosedFiniteChart K n h i := by
    apply (cancel_mono (C).hom.smoothLocus.ι).mp
    rw [Category.assoc]
    erw [completeClosedFiniteChart_inclusion]
    exact component_smoothIso_inv K n hn p q hp i
  rw [completeClosedSplitInclusion, ← Category.assoc, he]

end FLT.Mazur.PolygonInfinitesimalStages
