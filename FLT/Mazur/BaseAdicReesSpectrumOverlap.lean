/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpectrum
public import FLT.Mazur.BaseAdicReesOverlapCover

/-!
# Overlap maps with fixed spectrum sources

The common refinement charts and both overlap projections retain the same
geometric maps while using one named spectrum presentation throughout.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped TensorProduct

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R)

attribute [local irreducible] Scheme.Modules.pullback
attribute [local irreducible] modelMap
attribute [local irreducible] chartSpaceMap modelSheaf
attribute [local irreducible] modelAffineOverlap modelOverlapChart
attribute [local semireducible] modelSpectrum
attribute [local irreducible] AffineIteratedPullbackSections.compositeIso

/-- The first full-overlap projection with fixed spectrum target. -/
def spectrumOverlapFirst (U V : X.affineOpens) :
    modelOverlap f J U V ⟶ modelSpectrum f J U :=
  Limits.pullback.fst (chartSpaceMap f J U) (chartSpaceMap f J V)

/-- The second full-overlap projection with fixed spectrum target. -/
def spectrumOverlapSecond (U V : X.affineOpens) :
    modelOverlap f J U V ⟶ modelSpectrum f J V :=
  Limits.pullback.snd (chartSpaceMap f J U) (chartSpaceMap f J V)

/-- The common affine refinement chart with fixed spectrum source. -/
def spectrumOverlapChart {U V W : X.affineOpens} (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) :
    modelSpectrum f J W ⟶ modelOverlap f J U V :=
  modelOverlapChart f J i j

/-- The original inclusion remains an open immersion in this presentation. -/
instance spectrumMap_isOpenImmersion {U V : X.affineOpens} (i : U.1 ≤ V.1) :
    IsOpenImmersion (spectrumMap f J i) :=
  modelMap_isOpenImmersion f J i

/-- The original overlap chart remains an open immersion. -/
instance spectrumOverlapChart_isOpenImmersion {U V W : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) : IsOpenImmersion (spectrumOverlapChart f J i j) :=
  modelOverlapChart_isOpenImmersion f J i j

/-- The first projection of a refinement chart is its original inclusion. -/
@[reassoc]
lemma spectrumOverlapChart_first {U V W : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) :
    spectrumOverlapChart f J i j ≫ spectrumOverlapFirst f J U V = spectrumMap f J i :=
  modelOverlapChart_fst f J i j

/-- The second projection of a refinement chart is its original inclusion. -/
@[reassoc]
lemma spectrumOverlapChart_second {U V W : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) :
    spectrumOverlapChart f J i j ≫ spectrumOverlapSecond f J U V = spectrumMap f J j :=
  modelOverlapChart_snd f J i j

/-- Further refinements commute with the fixed-presentation overlap charts. -/
@[reassoc]
lemma spectrumOverlapChart_refine {U V W Z : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) (k : Z.1 ≤ W.1) :
    spectrumMap f J k ≫ spectrumOverlapChart f J i j =
      spectrumOverlapChart f J (k.trans i) (k.trans j) :=
  modelOverlapChart_refine f J i j k

/-- The fixed-presentation charts cover every point of the full overlap. -/
lemma spectrumOverlapChart_jointly_surjective (U V : X.affineOpens)
    (x : modelOverlap f J U V) :
    ∃ (W : X.affineOpens) (i : W.1 ≤ U.1) (j : W.1 ≤ V.1),
      x ∈ Set.range (spectrumOverlapChart f J i j) :=
  modelOverlapChart_jointly_surjective f J U V x

end FLT.Mazur.BaseAdicRees
