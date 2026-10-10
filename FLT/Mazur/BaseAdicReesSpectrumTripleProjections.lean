/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpectrumTripleOverlapCover

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

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (J : Ideal R)

attribute [local semireducible] modelSpectrum

/-- The first coordinate of the triple overlap. -/
def spectrumTripleFirstProjection (U V T : X.affineOpens) :
    spectrumTripleOverlap f J U V T ⟶ modelSpectrum f J U :=
  spectrumTripleFirstPairProjection f J U V T ≫ spectrumOverlapFirst f J U V

/-- The second coordinate of the triple overlap. -/
def spectrumTripleSecondProjection (U V T : X.affineOpens) :
    spectrumTripleOverlap f J U V T ⟶ modelSpectrum f J V :=
  spectrumTripleFirstPairProjection f J U V T ≫ spectrumOverlapSecond f J U V

/-- The first and third coordinates agree on the relative scheme. -/
lemma spectrumTripleFirstThird_condition (U V T : X.affineOpens) :
    spectrumTripleFirstProjection f J U V T ≫ spectrumSpaceMap f J U =
      spectrumTripleThirdProjection f J U V T ≫ spectrumSpaceMap f J T := by
  rw [spectrumTripleFirstProjection, Category.assoc]
  exact Limits.pullback.condition

/-- The second and third coordinates agree on the relative scheme. -/
lemma spectrumTripleSecondThird_condition (U V T : X.affineOpens) :
    spectrumTripleSecondProjection f J U V T ≫ spectrumSpaceMap f J V =
      spectrumTripleThirdProjection f J U V T ≫ spectrumSpaceMap f J T := by
  have h : spectrumOverlapFirst f J U V ≫ spectrumSpaceMap f J U =
      spectrumOverlapSecond f J U V ≫ spectrumSpaceMap f J V :=
    Limits.pullback.condition
  dsimp only [spectrumTripleSecondProjection]
  rw [Category.assoc, ← h, ← Category.assoc]
  exact spectrumTripleFirstThird_condition f J U V T

/-- Projection to the overlap of the first and third charts. -/
def spectrumTripleOuterPairProjection (U V T : X.affineOpens) :
    spectrumTripleOverlap f J U V T ⟶ modelOverlap f J U T :=
  Limits.pullback.lift (spectrumTripleFirstProjection f J U V T)
    (spectrumTripleThirdProjection f J U V T) (spectrumTripleFirstThird_condition f J U V T)

/-- Projection to the overlap of the second and third charts. -/
def spectrumTripleLastPairProjection (U V T : X.affineOpens) :
    spectrumTripleOverlap f J U V T ⟶ modelOverlap f J V T :=
  Limits.pullback.lift (spectrumTripleSecondProjection f J U V T)
    (spectrumTripleThirdProjection f J U V T) (spectrumTripleSecondThird_condition f J U V T)

/-- The outer pair retains the first coordinate. -/
@[reassoc]
lemma spectrumTripleOuterPairProjection_first (U V T : X.affineOpens) :
    spectrumTripleOuterPairProjection f J U V T ≫ spectrumOverlapFirst f J U T =
      spectrumTripleFirstProjection f J U V T := Limits.pullback.lift_fst _ _ _

/-- The outer pair retains the third coordinate. -/
@[reassoc]
lemma spectrumTripleOuterPairProjection_third (U V T : X.affineOpens) :
    spectrumTripleOuterPairProjection f J U V T ≫ spectrumOverlapSecond f J U T =
      spectrumTripleThirdProjection f J U V T := Limits.pullback.lift_snd _ _ _

/-- The last pair retains the second coordinate. -/
@[reassoc]
lemma spectrumTripleLastPairProjection_second (U V T : X.affineOpens) :
    spectrumTripleLastPairProjection f J U V T ≫ spectrumOverlapFirst f J V T =
      spectrumTripleSecondProjection f J U V T := Limits.pullback.lift_fst _ _ _

/-- The last pair retains the third coordinate. -/
@[reassoc]
lemma spectrumTripleLastPairProjection_third (U V T : X.affineOpens) :
    spectrumTripleLastPairProjection f J U V T ≫ spectrumOverlapSecond f J V T =
      spectrumTripleThirdProjection f J U V T := Limits.pullback.lift_snd _ _ _

/-- A common chart has its original first coordinate. -/
@[reassoc]
lemma spectrumTripleOverlapChart_first {U V T W : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) (k : W.1 ≤ T.1) :
    spectrumTripleOverlapChart f J i j k ≫ spectrumTripleFirstProjection f J U V T =
      spectrumMap f J i := by
  rw [spectrumTripleFirstProjection, spectrumTripleOverlapChart_firstPair_assoc,
    spectrumOverlapChart_first]

/-- A common chart has its original second coordinate. -/
@[reassoc]
lemma spectrumTripleOverlapChart_second {U V T W : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) (k : W.1 ≤ T.1) :
    spectrumTripleOverlapChart f J i j k ≫ spectrumTripleSecondProjection f J U V T =
      spectrumMap f J j := by
  rw [spectrumTripleSecondProjection, spectrumTripleOverlapChart_firstPair_assoc,
    spectrumOverlapChart_second]

/-- The outer pair projection recovers the original outer pair chart. -/
@[reassoc]
lemma spectrumTripleOverlapChart_outerPair {U V T W : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) (k : W.1 ≤ T.1) :
    spectrumTripleOverlapChart f J i j k ≫ spectrumTripleOuterPairProjection f J U V T =
      spectrumOverlapChart f J i k := by
  apply Limits.pullback.hom_ext
  · change (spectrumTripleOverlapChart f J i j k ≫
        spectrumTripleOuterPairProjection f J U V T) ≫
        spectrumOverlapFirst f J U T =
      spectrumOverlapChart f J i k ≫ spectrumOverlapFirst f J U T
    rw [Category.assoc, spectrumTripleOuterPairProjection_first,
      spectrumTripleOverlapChart_first, spectrumOverlapChart_first]
  · change (spectrumTripleOverlapChart f J i j k ≫
        spectrumTripleOuterPairProjection f J U V T) ≫
        spectrumOverlapSecond f J U T =
      spectrumOverlapChart f J i k ≫ spectrumOverlapSecond f J U T
    rw [Category.assoc, spectrumTripleOuterPairProjection_third,
      spectrumTripleOverlapChart_third, spectrumOverlapChart_second]

/-- The last pair projection recovers the original last pair chart. -/
@[reassoc]
lemma spectrumTripleOverlapChart_lastPair {U V T W : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) (k : W.1 ≤ T.1) :
    spectrumTripleOverlapChart f J i j k ≫ spectrumTripleLastPairProjection f J U V T =
      spectrumOverlapChart f J j k := by
  apply Limits.pullback.hom_ext
  · change (spectrumTripleOverlapChart f J i j k ≫
        spectrumTripleLastPairProjection f J U V T) ≫
        spectrumOverlapFirst f J V T =
      spectrumOverlapChart f J j k ≫ spectrumOverlapFirst f J V T
    rw [Category.assoc, spectrumTripleLastPairProjection_second,
      spectrumTripleOverlapChart_second, spectrumOverlapChart_first]
  · change (spectrumTripleOverlapChart f J i j k ≫
        spectrumTripleLastPairProjection f J U V T) ≫
        spectrumOverlapSecond f J V T =
      spectrumOverlapChart f J j k ≫ spectrumOverlapSecond f J V T
    rw [Category.assoc, spectrumTripleLastPairProjection_third,
      spectrumTripleOverlapChart_third, spectrumOverlapChart_second]

end FLT.Mazur.BaseAdicRees
