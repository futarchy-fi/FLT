/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpectrumTripleSheafMaps

/-!
# Affine restrictions of triple coefficient maps

The three normalized global comparisons recover the original affine maps
on every common refinement of the three tensor charts.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.BaseAdicRees

open SheafPullbackMapNormalization SheafPullbackPathComparison

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

attribute [local irreducible] Scheme.Modules.pullback spectrumMap
attribute [local irreducible] spectrumOverlapChart spectrumSpaceMap
attribute [local irreducible] spectrumSheaf spectrumAffineOverlap
attribute [local irreducible] AffineIteratedPullbackSections.compositeIso
attribute [local irreducible] spectrumOverlapSheafIso


/-- The first comparison restricts to its normalized affine pair map. -/
lemma spectrumTripleFirstSheafMap_chart {U V T W : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) (k : W.1 ≤ T.1) :
    (pullback (spectrumTripleOverlapChart f J i j k)).map
        (spectrumTripleFirstSheafMap f J M U V T) ≫
        (comparison (spectrumTripleOverlapChart f J i j k)
          (spectrumTripleSecondProjection f J U V T) (spectrumMap f J j)
          (spectrumTripleOverlapChart_second f J i j k)).hom.app
            (spectrumSheaf f J M V) =
      (comparison (spectrumTripleOverlapChart f J i j k)
        (spectrumTripleFirstProjection f J U V T) (spectrumMap f J i)
        (spectrumTripleOverlapChart_first f J i j k)).hom.app
          (spectrumSheaf f J M U) ≫
        spectrumOverlapAffineMap f J M i j := by
  exact normalize_refine (spectrumTripleFirstPairProjection f J U V T)
    (spectrumOverlapFirst f J U V) (spectrumOverlapSecond f J U V)
    (spectrumTripleFirstProjection f J U V T) (spectrumTripleSecondProjection f J U V T)
    rfl rfl
    (spectrumTripleOverlapChart f J i j k) (spectrumOverlapChart f J i j)
    (spectrumTripleOverlapChart_firstPair f J i j k)
    (spectrumMap f J i) (spectrumMap f J j)
    (spectrumTripleOverlapChart_first f J i j k)
    (spectrumTripleOverlapChart_second f J i j k)
    (spectrumOverlapChart_first f J i j)
    (spectrumOverlapChart_second f J i j) (spectrumOverlapSheafIso f J M U V).hom

/-- The last comparison restricts to its normalized affine pair map. -/
lemma spectrumTripleLastSheafMap_chart {U V T W : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) (k : W.1 ≤ T.1) :
    (pullback (spectrumTripleOverlapChart f J i j k)).map
        (spectrumTripleLastSheafMap f J M U V T) ≫
        (comparison (spectrumTripleOverlapChart f J i j k)
          (spectrumTripleThirdProjection f J U V T) (spectrumMap f J k)
          (spectrumTripleOverlapChart_third f J i j k)).hom.app
            (spectrumSheaf f J M T) =
      (comparison (spectrumTripleOverlapChart f J i j k)
        (spectrumTripleSecondProjection f J U V T) (spectrumMap f J j)
        (spectrumTripleOverlapChart_second f J i j k)).hom.app
          (spectrumSheaf f J M V) ≫
        spectrumOverlapAffineMap f J M j k := by
  exact normalize_refine (spectrumTripleLastPairProjection f J U V T)
    (spectrumOverlapFirst f J V T) (spectrumOverlapSecond f J V T)
    (spectrumTripleSecondProjection f J U V T) (spectrumTripleThirdProjection f J U V T)
    (spectrumTripleLastPairProjection_second f J U V T)
    (spectrumTripleLastPairProjection_third f J U V T)
    (spectrumTripleOverlapChart f J i j k) (spectrumOverlapChart f J j k)
    (spectrumTripleOverlapChart_lastPair f J i j k)
    (spectrumMap f J j) (spectrumMap f J k)
    (spectrumTripleOverlapChart_second f J i j k)
    (spectrumTripleOverlapChart_third f J i j k)
    (spectrumOverlapChart_first f J j k)
    (spectrumOverlapChart_second f J j k) (spectrumOverlapSheafIso f J M V T).hom

/-- The outer comparison restricts to its normalized affine pair map. -/
lemma spectrumTripleOuterSheafMap_chart {U V T W : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) (k : W.1 ≤ T.1) :
    (pullback (spectrumTripleOverlapChart f J i j k)).map
        (spectrumTripleOuterSheafMap f J M U V T) ≫
        (comparison (spectrumTripleOverlapChart f J i j k)
          (spectrumTripleThirdProjection f J U V T) (spectrumMap f J k)
          (spectrumTripleOverlapChart_third f J i j k)).hom.app
            (spectrumSheaf f J M T) =
      (comparison (spectrumTripleOverlapChart f J i j k)
        (spectrumTripleFirstProjection f J U V T) (spectrumMap f J i)
        (spectrumTripleOverlapChart_first f J i j k)).hom.app
          (spectrumSheaf f J M U) ≫
        spectrumOverlapAffineMap f J M i k := by
  exact normalize_refine (spectrumTripleOuterPairProjection f J U V T)
    (spectrumOverlapFirst f J U T) (spectrumOverlapSecond f J U T)
    (spectrumTripleFirstProjection f J U V T) (spectrumTripleThirdProjection f J U V T)
    (spectrumTripleOuterPairProjection_first f J U V T)
    (spectrumTripleOuterPairProjection_third f J U V T)
    (spectrumTripleOverlapChart f J i j k) (spectrumOverlapChart f J i k)
    (spectrumTripleOverlapChart_outerPair f J i j k)
    (spectrumMap f J i) (spectrumMap f J k)
    (spectrumTripleOverlapChart_first f J i j k)
    (spectrumTripleOverlapChart_third f J i j k)
    (spectrumOverlapChart_first f J i k)
    (spectrumOverlapChart_second f J i k) (spectrumOverlapSheafIso f J M U T).hom

end FLT.Mazur.BaseAdicRees
