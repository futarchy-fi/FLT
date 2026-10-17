/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedSplitParameter

/-!
# The full old action input is the actual original closed product

The split smooth parameter and the whole original polygon give a Cartesian
closed-fiber square for the original action input, retaining both projections.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "C" => PolygonCyclicAtlas.polygon K n h
local notation "G" => PolygonSplitGroup.model K n
local notation "M" => completeOriginalSmoothOver K n h
local notation "X" => completeOriginalWholeOver K n h
local notation "g" => completeClosedSplitInclusion K n h
local notation "j" => completeClosedFiberInclusion K n h
local notation "b" => completeClosedBase K

/-- The full old smooth-by-whole input maps into the original complete action input. -/
def completeClosedActionInput : ((G) ⊗ (C)).left ⟶ ((M) ⊗ (X)).left :=
  pullback.lift ((fst (G) (C)).left ≫ (g)) ((snd (G) (C)).left ≫ (j)) (by
    have hw : (j) ≫ (X).hom = (C).hom ≫ (b) :=
      (completeClosedFiber_isPullback K n h).w
    rw [Category.assoc, completeClosedSplitInclusion_base, Category.assoc, hw]
    have hf : (fst (G) (C)).left ≫ (G).hom = (snd (G) (C)).left ≫ (C).hom :=
      (fst (G) (C)).w.trans (snd (G) (C)).w.symm
    simpa only [Category.assoc] using congrArg (· ≫ (b)) hf)

/-- The first projection is the original full closed smooth parameter inclusion. -/
@[reassoc] theorem completeClosedActionInput_fst :
    completeClosedActionInput K n h ≫ (fst (M) (X)).left =
      (fst (G) (C)).left ≫ (g) := pullback.lift_fst _ _ _

/-- The second projection retains the entire original closed polygon. -/
@[reassoc] theorem completeClosedActionInput_snd :
    completeClosedActionInput K n h ≫ (snd (M) (X)).left =
      (snd (G) (C)).left ≫ (j) := pullback.lift_snd _ _ _

/-- The actual original input square is Cartesian over the whole closed polygon. -/
theorem completeClosedActionInput_isPullback :
    IsPullback (completeClosedActionInput K n h) (snd (G) (C)).left
      (snd (M) (X)).left (j) := by
  have hp := (IsPullback.of_hasPullback (G).hom (C).hom).paste_horiz
    (completeClosedSplitInclusion_isPullback K n h)
  have he : IsPullback
      (completeClosedActionInput K n h ≫ (fst (M) (X)).left)
      (snd (G) (C)).left (M).hom ((j) ≫ (X).hom) := by
    have hw : (j) ≫ (X).hom = (C).hom ≫ (b) :=
      (completeClosedFiber_isPullback K n h).w
    rw [completeClosedActionInput_fst, hw]
    exact hp
  exact he.of_right (completeClosedActionInput_snd K n h)
    (IsPullback.of_hasPullback (M).hom (X).hom)

/-- The full closed input is the complete action product's actual coefficient base change. -/
theorem completeClosedActionInput_base_isPullback :
    IsPullback (completeClosedActionInput K n h) ((snd (G) (C)).left ≫ (C).hom)
      ((snd (M) (X)).left ≫ (X).hom) (b) :=
  (completeClosedActionInput_isPullback K n h).paste_vert
    (completeClosedFiber_isPullback K n h)

/-- The full old input is isomorphic to the actual original closed input fiber product. -/
def completeClosedActionProductIso : ((G) ⊗ (C)).left ≅
    pullback ((snd (M) (X)).left ≫ (X).hom) (b) :=
  (completeClosedActionInput_base_isPullback K n h).isoPullback

/-- The product identification preserves the actual action input inclusion. -/
@[reassoc] theorem completeClosedActionProductIso_fst :
    (completeClosedActionProductIso K n h).hom ≫ pullback.fst _ _ =
      completeClosedActionInput K n h :=
  (completeClosedActionInput_base_isPullback K n h).isoPullback_hom_fst

/-- The product identification preserves the original closed coefficient projection. -/
@[reassoc] theorem completeClosedActionProductIso_snd :
    (completeClosedActionProductIso K n h).hom ≫ pullback.snd _ _ =
      (snd (G) (C)).left ≫ (C).hom :=
  (completeClosedActionInput_base_isPullback K n h).isoPullback_hom_snd

end FLT.Mazur.PolygonInfinitesimalStages
