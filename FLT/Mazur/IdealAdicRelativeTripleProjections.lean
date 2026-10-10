/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeTripleOverlapCover

/-!
# Pair projections from the relative triple overlap

The three pair maps have common coordinate projections and recover the
original pair charts on every common affine refinement.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- The first coordinate of the triple overlap. -/
def relativeTripleFirstProjection (U V T : X.affineOpens) :
    relativeTensorTripleOverlap J f U V T ⟶ Spec (.of (RelativeAlgebra J f U)) :=
  relativeTripleFirstPairProjection J f U V T ≫ relativeOverlapFirstProjection J f U V

/-- The second coordinate of the triple overlap. -/
def relativeTripleSecondProjection (U V T : X.affineOpens) :
    relativeTensorTripleOverlap J f U V T ⟶ Spec (.of (RelativeAlgebra J f V)) :=
  relativeTripleFirstPairProjection J f U V T ≫ relativeOverlapSecondProjection J f U V

/-- The first and third coordinates agree on the relative scheme. -/
lemma relativeTripleFirstThird_condition (U V T : X.affineOpens) :
    relativeTripleFirstProjection J f U V T ≫ relativeTensorChart J f U =
      relativeTripleThirdProjection J f U V T ≫ relativeTensorChart J f T := by
  rw [relativeTripleFirstProjection, Category.assoc]
  exact Limits.pullback.condition

/-- The second and third coordinates agree on the relative scheme. -/
lemma relativeTripleSecondThird_condition (U V T : X.affineOpens) :
    relativeTripleSecondProjection J f U V T ≫ relativeTensorChart J f V =
      relativeTripleThirdProjection J f U V T ≫ relativeTensorChart J f T := by
  have h : relativeOverlapFirstProjection J f U V ≫ relativeTensorChart J f U =
      relativeOverlapSecondProjection J f U V ≫ relativeTensorChart J f V :=
    Limits.pullback.condition
  dsimp only [relativeTripleSecondProjection]
  rw [Category.assoc, ← h, ← Category.assoc]
  exact relativeTripleFirstThird_condition J f U V T

/-- Projection to the overlap of the first and third charts. -/
def relativeTripleOuterPairProjection (U V T : X.affineOpens) :
    relativeTensorTripleOverlap J f U V T ⟶ relativeTensorOverlap J f U T :=
  Limits.pullback.lift (relativeTripleFirstProjection J f U V T)
    (relativeTripleThirdProjection J f U V T) (relativeTripleFirstThird_condition J f U V T)

/-- Projection to the overlap of the second and third charts. -/
def relativeTripleLastPairProjection (U V T : X.affineOpens) :
    relativeTensorTripleOverlap J f U V T ⟶ relativeTensorOverlap J f V T :=
  Limits.pullback.lift (relativeTripleSecondProjection J f U V T)
    (relativeTripleThirdProjection J f U V T) (relativeTripleSecondThird_condition J f U V T)

/-- The outer pair retains the first coordinate. -/
@[reassoc]
lemma relativeTripleOuterPairProjection_first (U V T : X.affineOpens) :
    relativeTripleOuterPairProjection J f U V T ≫ relativeOverlapFirstProjection J f U T =
      relativeTripleFirstProjection J f U V T := Limits.pullback.lift_fst _ _ _

/-- The outer pair retains the third coordinate. -/
@[reassoc]
lemma relativeTripleOuterPairProjection_third (U V T : X.affineOpens) :
    relativeTripleOuterPairProjection J f U V T ≫ relativeOverlapSecondProjection J f U T =
      relativeTripleThirdProjection J f U V T := Limits.pullback.lift_snd _ _ _

/-- The last pair retains the second coordinate. -/
@[reassoc]
lemma relativeTripleLastPairProjection_second (U V T : X.affineOpens) :
    relativeTripleLastPairProjection J f U V T ≫ relativeOverlapFirstProjection J f V T =
      relativeTripleSecondProjection J f U V T := Limits.pullback.lift_fst _ _ _

/-- The last pair retains the third coordinate. -/
@[reassoc]
lemma relativeTripleLastPairProjection_third (U V T : X.affineOpens) :
    relativeTripleLastPairProjection J f U V T ≫ relativeOverlapSecondProjection J f V T =
      relativeTripleThirdProjection J f U V T := Limits.pullback.lift_snd _ _ _

/-- A common chart has its original first coordinate. -/
@[reassoc]
lemma relativeTensorTripleOverlapChart_first {U V T W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (k : W.1 ⟶ T.1) :
    relativeTensorTripleOverlapChart J f i j k ≫ relativeTripleFirstProjection J f U V T =
      relativeTensorTransition J f i := by
  rw [relativeTripleFirstProjection, relativeTensorTripleOverlapChart_firstPair_assoc,
    relativeOverlapFirstProjection_chart]

/-- A common chart has its original second coordinate. -/
@[reassoc]
lemma relativeTensorTripleOverlapChart_second {U V T W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (k : W.1 ⟶ T.1) :
    relativeTensorTripleOverlapChart J f i j k ≫ relativeTripleSecondProjection J f U V T =
      relativeTensorTransition J f j := by
  rw [relativeTripleSecondProjection, relativeTensorTripleOverlapChart_firstPair_assoc,
    relativeOverlapSecondProjection_chart]

/-- The outer pair projection recovers the original outer pair chart. -/
@[reassoc]
lemma relativeTensorTripleOverlapChart_outerPair {U V T W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (k : W.1 ⟶ T.1) :
    relativeTensorTripleOverlapChart J f i j k ≫ relativeTripleOuterPairProjection J f U V T =
      relativeTensorOverlapChart J f i k := by
  apply Limits.pullback.hom_ext
  · change (relativeTensorTripleOverlapChart J f i j k ≫
        relativeTripleOuterPairProjection J f U V T) ≫
        relativeOverlapFirstProjection J f U T =
      relativeTensorOverlapChart J f i k ≫ relativeOverlapFirstProjection J f U T
    rw [Category.assoc, relativeTripleOuterPairProjection_first,
      relativeTensorTripleOverlapChart_first, relativeOverlapFirstProjection_chart]
  · change (relativeTensorTripleOverlapChart J f i j k ≫
        relativeTripleOuterPairProjection J f U V T) ≫
        relativeOverlapSecondProjection J f U T =
      relativeTensorOverlapChart J f i k ≫ relativeOverlapSecondProjection J f U T
    rw [Category.assoc, relativeTripleOuterPairProjection_third,
      relativeTensorTripleOverlapChart_third, relativeOverlapSecondProjection_chart]

/-- The last pair projection recovers the original last pair chart. -/
@[reassoc]
lemma relativeTensorTripleOverlapChart_lastPair {U V T W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (k : W.1 ⟶ T.1) :
    relativeTensorTripleOverlapChart J f i j k ≫ relativeTripleLastPairProjection J f U V T =
      relativeTensorOverlapChart J f j k := by
  apply Limits.pullback.hom_ext
  · change (relativeTensorTripleOverlapChart J f i j k ≫
        relativeTripleLastPairProjection J f U V T) ≫
        relativeOverlapFirstProjection J f V T =
      relativeTensorOverlapChart J f j k ≫ relativeOverlapFirstProjection J f V T
    rw [Category.assoc, relativeTripleLastPairProjection_second,
      relativeTensorTripleOverlapChart_second, relativeOverlapFirstProjection_chart]
  · change (relativeTensorTripleOverlapChart J f i j k ≫
        relativeTripleLastPairProjection J f U V T) ≫
        relativeOverlapSecondProjection J f V T =
      relativeTensorOverlapChart J f j k ≫ relativeOverlapSecondProjection J f V T
    rw [Category.assoc, relativeTripleLastPairProjection_third,
      relativeTensorTripleOverlapChart_third, relativeOverlapSecondProjection_chart]

end FLT.Mazur.IdealAdicGradedPullback
