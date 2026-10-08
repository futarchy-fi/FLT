/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpectrumOverlap

/-!
# Common affine refinements of three relative Rees charts

The fixed spectrum charts retain the original map to the relative space.
Triple intersections have a common affine refinement at every point.
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

/-- The original relative chart inclusion with its fixed spectrum source. -/
def spectrumSpaceMap (V : X.affineOpens) : modelSpectrum f J V ⟶ relativeSpace f J :=
  chartSpaceMap f J V

/-- Each fixed-presentation chart is an open subscheme of the relative Rees space. -/
instance spectrumSpaceMap_isOpenImmersion (V : X.affineOpens) :
    IsOpenImmersion (spectrumSpaceMap f J V) := chartSpaceMap_isOpenImmersion f J V

/-- Affine inclusions commute with the actual relative chart maps. -/
@[reassoc]
lemma spectrumMap_chart {U V : X.affineOpens} (i : U.1 ≤ V.1) :
    spectrumMap f J i ≫ spectrumSpaceMap f J V = spectrumSpaceMap f J U := by
  unfold spectrumMap modelMap spectrumSpaceMap
  exact relativeRingRestriction_spec f J i

/-- Both overlap coordinates give the same point of the relative space. -/
lemma spectrumOverlap_condition (U V : X.affineOpens) :
    spectrumOverlapFirst f J U V ≫ spectrumSpaceMap f J U =
      spectrumOverlapSecond f J U V ≫ spectrumSpaceMap f J V :=
  Limits.pullback.condition

/-- Membership in the fixed-presentation chart is detected on the original scheme. -/
lemma spectrumSpaceMap_mem_range_iff (U : X.affineOpens) (x : relativeSpace f J) :
    x ∈ Set.range (spectrumSpaceMap f J U) ↔
      Limits.pullback.fst f (baseMap J) x ∈ U.1 :=
  chartSpaceMap_mem_range_iff f J U x

/-- Every point in three relative charts has a common original affine refinement. -/
lemma spectrumSpaceMap_exists_triple_refinement (U V T : X.affineOpens)
    (x : relativeSpace f J)
    (hU : x ∈ Set.range (spectrumSpaceMap f J U))
    (hV : x ∈ Set.range (spectrumSpaceMap f J V))
    (hT : x ∈ Set.range (spectrumSpaceMap f J T)) :
    ∃ (W : X.affineOpens) (_i : W.1 ≤ U.1) (_j : W.1 ≤ V.1) (_k : W.1 ≤ T.1),
      x ∈ Set.range (spectrumSpaceMap f J W) := by
  let z := Limits.pullback.fst f (baseMap J) x
  have hz : z ∈ (U.1 ⊓ V.1 ⊓ T.1 : X.Opens) :=
    ⟨⟨(spectrumSpaceMap_mem_range_iff f J U x).mp hU,
      (spectrumSpaceMap_mem_range_iff f J V x).mp hV⟩,
      (spectrumSpaceMap_mem_range_iff f J T x).mp hT⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hzW, hsub : W ≤ U.1 ⊓ V.1 ⊓ T.1⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hz (U.1 ⊓ V.1 ⊓ T.1).2
  exact ⟨⟨W, hW⟩, hsub.trans (inf_le_left.trans inf_le_left),
    hsub.trans (inf_le_left.trans inf_le_right), hsub.trans inf_le_right,
    (spectrumSpaceMap_mem_range_iff f J ⟨W, hW⟩ x).mpr hzW⟩

end FLT.Mazur.BaseAdicRees
