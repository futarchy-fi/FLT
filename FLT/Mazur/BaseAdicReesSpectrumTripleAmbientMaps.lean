/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpectrumAmbientSheaf
public import FLT.Mazur.BaseAdicReesSpectrumTripleSheafMaps
public import FLT.Mazur.ModuleSheafOverlapCoordinateRefinement

/-!
# Ambient triple coefficient maps

Normalize the ambient pair comparisons to the triple structure map and
identify them with the previously constructed coordinate coefficient maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.BaseAdicRees

open ModuleSheafOverlapImageTransition SheafPullbackMapNormalization

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

attribute [local instance] spectrumSpaceMap_isOpenImmersion
attribute [local irreducible] Scheme.Modules.pullback spectrumSheaf
attribute [local irreducible] spectrumOverlapSheafIso spectrumSpaceMap
attribute [local irreducible] spectrumMap spectrumOverlapChart
attribute [local irreducible] spectrumAffineOverlap
attribute [local irreducible] spectrumTripleLastPairProjection spectrumTripleOuterPairProjection

variable (U V T : X.affineOpens)

/-- The first ambient pair comparison pulled back to the triple overlap. -/
def spectrumTripleFirstAmbientMap :
    (pullback (spectrumTripleToScheme f J U V T)).obj (spectrumAmbientSheaf f J M U) ⟶
      (pullback (spectrumTripleToScheme f J U V T)).obj (spectrumAmbientSheaf f J M V) :=
  SheafPullbackMapNormalization.normalize (M := (pushforward (spectrumSpaceMap f J U)).obj
      (spectrumSheaf f J M U))
    (N := (pushforward (spectrumSpaceMap f J V)).obj
      (spectrumSheaf f J M V)) (spectrumTripleFirstPairProjection f J U V T)
    (spectrumOverlapToSpace f J U V) (spectrumOverlapToSpace f J U V)
    (spectrumTripleToScheme f J U V T) (spectrumTripleToScheme f J U V T)
    rfl rfl
    (spectrumOverlapAmbientSheafIso f J M U V).hom

/-- The first ambient triple map recovers its original coordinate comparison. -/
@[reassoc]
lemma spectrumTripleFirstAmbientMap_coordinate :
    spectrumTripleFirstAmbientMap f J M U V T ≫
        (spectrumTripleSecondAmbientCoordinate f J M U V T).hom =
      (spectrumTripleFirstAmbientCoordinate f J M U V T).hom ≫
        spectrumTripleFirstSheafMap f J M U V T := by
  unfold spectrumTripleFirstAmbientMap spectrumTripleSecondAmbientCoordinate
    spectrumTripleFirstAmbientCoordinate spectrumOverlapAmbientSheafIso
    spectrumTripleFirstSheafMap spectrumAmbientSheaf
  exact ambientIso_refine_coordinate
    (M := spectrumSheaf f J M U)
    (N := spectrumSheaf f J M V)
    (spectrumTripleFirstPairProjection f J U V T)
    (spectrumSpaceMap f J U) (spectrumSpaceMap f J V)
    (spectrumOverlapFirst f J U V)
    (spectrumOverlapSecond f J U V) (spectrumOverlapToSpace f J U V)
    rfl (spectrumOverlap_condition f J U V).symm
    (spectrumTripleFirstProjection f J U V T) (spectrumTripleSecondProjection f J U V T)
    (spectrumTripleToScheme f J U V T) rfl rfl
    rfl (spectrumTripleFirstProjection_toScheme f J U V T)
    (spectrumTripleSecondProjection_toScheme f J U V T) (spectrumOverlapSheafIso f J M U V)

/-- The last ambient pair comparison pulled back to the triple overlap. -/
def spectrumTripleLastAmbientMap :
    (pullback (spectrumTripleToScheme f J U V T)).obj (spectrumAmbientSheaf f J M V) ⟶
      (pullback (spectrumTripleToScheme f J U V T)).obj (spectrumAmbientSheaf f J M T) :=
  SheafPullbackMapNormalization.normalize (M := (pushforward (spectrumSpaceMap f J V)).obj
      (spectrumSheaf f J M V))
    (N := (pushforward (spectrumSpaceMap f J T)).obj
      (spectrumSheaf f J M T)) (spectrumTripleLastPairProjection f J U V T)
    (spectrumOverlapToSpace f J V T) (spectrumOverlapToSpace f J V T)
    (spectrumTripleToScheme f J U V T) (spectrumTripleToScheme f J U V T)
    (spectrumTripleLastPairProjection_toScheme f J U V T)
    (spectrumTripleLastPairProjection_toScheme f J U V T)
    (spectrumOverlapAmbientSheafIso f J M V T).hom

/-- The last ambient triple map recovers its original coordinate comparison. -/
@[reassoc]
lemma spectrumTripleLastAmbientMap_coordinate :
    spectrumTripleLastAmbientMap f J M U V T ≫
        (spectrumTripleThirdAmbientCoordinate f J M U V T).hom =
      (spectrumTripleSecondAmbientCoordinate f J M U V T).hom ≫
        spectrumTripleLastSheafMap f J M U V T := by
  unfold spectrumTripleLastAmbientMap spectrumTripleThirdAmbientCoordinate
    spectrumTripleSecondAmbientCoordinate spectrumOverlapAmbientSheafIso
    spectrumTripleLastSheafMap spectrumAmbientSheaf
  exact ambientIso_refine_coordinate
    (M := spectrumSheaf f J M V)
    (N := spectrumSheaf f J M T)
    (spectrumTripleLastPairProjection f J U V T)
    (spectrumSpaceMap f J V) (spectrumSpaceMap f J T)
    (spectrumOverlapFirst f J V T)
    (spectrumOverlapSecond f J V T) (spectrumOverlapToSpace f J V T)
    rfl (spectrumOverlap_condition f J V T).symm
    (spectrumTripleSecondProjection f J U V T) (spectrumTripleThirdProjection f J U V T)
    (spectrumTripleToScheme f J U V T) (spectrumTripleLastPairProjection_second f J U V T)
    (spectrumTripleLastPairProjection_third f J U V T)
    (spectrumTripleLastPairProjection_toScheme f J U V T)
    (spectrumTripleSecondProjection_toScheme f J U V T)
    (spectrumTripleThirdProjection_toScheme f J U V T) (spectrumOverlapSheafIso f J M V T)

/-- The outer ambient pair comparison pulled back to the triple overlap. -/
def spectrumTripleOuterAmbientMap :
    (pullback (spectrumTripleToScheme f J U V T)).obj (spectrumAmbientSheaf f J M U) ⟶
      (pullback (spectrumTripleToScheme f J U V T)).obj (spectrumAmbientSheaf f J M T) :=
  SheafPullbackMapNormalization.normalize (M := (pushforward (spectrumSpaceMap f J U)).obj
      (spectrumSheaf f J M U))
    (N := (pushforward (spectrumSpaceMap f J T)).obj
      (spectrumSheaf f J M T)) (spectrumTripleOuterPairProjection f J U V T)
    (spectrumOverlapToSpace f J U T) (spectrumOverlapToSpace f J U T)
    (spectrumTripleToScheme f J U V T) (spectrumTripleToScheme f J U V T)
    (spectrumTripleOuterPairProjection_toScheme f J U V T)
    (spectrumTripleOuterPairProjection_toScheme f J U V T)
    (spectrumOverlapAmbientSheafIso f J M U T).hom

/-- The outer ambient triple map recovers its original coordinate comparison. -/
@[reassoc]
lemma spectrumTripleOuterAmbientMap_coordinate :
    spectrumTripleOuterAmbientMap f J M U V T ≫
        (spectrumTripleThirdAmbientCoordinate f J M U V T).hom =
      (spectrumTripleFirstAmbientCoordinate f J M U V T).hom ≫
        spectrumTripleOuterSheafMap f J M U V T := by
  unfold spectrumTripleOuterAmbientMap spectrumTripleThirdAmbientCoordinate
    spectrumTripleFirstAmbientCoordinate spectrumOverlapAmbientSheafIso
    spectrumTripleOuterSheafMap spectrumAmbientSheaf
  exact ambientIso_refine_coordinate
    (M := spectrumSheaf f J M U)
    (N := spectrumSheaf f J M T)
    (spectrumTripleOuterPairProjection f J U V T)
    (spectrumSpaceMap f J U) (spectrumSpaceMap f J T)
    (spectrumOverlapFirst f J U T)
    (spectrumOverlapSecond f J U T) (spectrumOverlapToSpace f J U T)
    rfl (spectrumOverlap_condition f J U T).symm
    (spectrumTripleFirstProjection f J U V T) (spectrumTripleThirdProjection f J U V T)
    (spectrumTripleToScheme f J U V T) (spectrumTripleOuterPairProjection_first f J U V T)
    (spectrumTripleOuterPairProjection_third f J U V T)
    (spectrumTripleOuterPairProjection_toScheme f J U V T)
    (spectrumTripleFirstProjection_toScheme f J U V T)
    (spectrumTripleThirdProjection_toScheme f J U V T) (spectrumOverlapSheafIso f J M U T)

end FLT.Mazur.BaseAdicRees
