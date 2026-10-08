/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpectrumImageSheafTransition
public import FLT.Mazur.BaseAdicReesSpectrumTripleImageOpen

/-!
# Ambient coefficient comparisons and triple coordinates

The chart pushforwards have actual overlap comparisons. Their pullbacks to
the triple overlap recover the three original coordinate coefficient sheaves.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.BaseAdicRees

open ModuleSheafOverlapImageTransition

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

attribute [local instance] spectrumSpaceMap_isOpenImmersion
attribute [local irreducible] Scheme.Modules.pullback spectrumSheaf
attribute [local irreducible] spectrumOverlapSheafIso

/-- The ambient module obtained by pushing forward one tensor-chart coefficient sheaf. -/
def spectrumAmbientSheaf (U : X.affineOpens) : (relativeSpace f J).Modules :=
  (pushforward (spectrumSpaceMap f J U)).obj (spectrumSheaf f J M U)

/-- The pair comparison on pullbacks of the ambient coefficient modules. -/
def spectrumOverlapAmbientSheafIso (U V : X.affineOpens) :
    (pullback (spectrumOverlapToSpace f J U V)).obj (spectrumAmbientSheaf f J M U) ≅
      (pullback (spectrumOverlapToSpace f J U V)).obj (spectrumAmbientSheaf f J M V) :=
  ambientIso (spectrumSpaceMap f J U) (spectrumSpaceMap f J V)
    (spectrumOverlapFirst f J U V) (spectrumOverlapSecond f J U V)
    (spectrumOverlapToSpace f J U V) rfl (spectrumOverlap_condition f J U V).symm
    (spectrumOverlapSheafIso f J M U V)

omit [IsLocallyNoetherian X] in
/-- The first triple coordinate has the triple structure morphism. -/
@[reassoc]
lemma spectrumTripleFirstProjection_toScheme (U V T : X.affineOpens) :
    spectrumTripleFirstProjection f J U V T ≫ spectrumSpaceMap f J U =
      spectrumTripleToScheme f J U V T := Category.assoc _ _ _

omit [IsLocallyNoetherian X] in
/-- The second triple coordinate has the triple structure morphism. -/
@[reassoc]
lemma spectrumTripleSecondProjection_toScheme (U V T : X.affineOpens) :
    spectrumTripleSecondProjection f J U V T ≫ spectrumSpaceMap f J V =
      spectrumTripleToScheme f J U V T := by
  rw [spectrumTripleSecondThird_condition, ← spectrumTripleFirstThird_condition,
    spectrumTripleFirstProjection_toScheme]

omit [IsLocallyNoetherian X] in
/-- The third triple coordinate has the triple structure morphism. -/
@[reassoc]
lemma spectrumTripleThirdProjection_toScheme (U V T : X.affineOpens) :
    spectrumTripleThirdProjection f J U V T ≫ spectrumSpaceMap f J T =
      spectrumTripleToScheme f J U V T := by
  rw [← spectrumTripleFirstThird_condition, spectrumTripleFirstProjection_toScheme]

/-- Recover the first coordinate coefficient sheaf on the triple overlap. -/
def spectrumTripleFirstAmbientCoordinate (U V T : X.affineOpens) :
    (pullback (spectrumTripleToScheme f J U V T)).obj (spectrumAmbientSheaf f J M U) ≅
      (pullback (spectrumTripleFirstProjection f J U V T)).obj
        (spectrumSheaf f J M U) :=
  coordinateIso (spectrumTripleFirstProjection f J U V T) (spectrumSpaceMap f J U)
    (spectrumTripleToScheme f J U V T) (spectrumTripleFirstProjection_toScheme f J U V T)
    (spectrumSheaf f J M U)

/-- Recover the second coordinate coefficient sheaf on the triple overlap. -/
def spectrumTripleSecondAmbientCoordinate (U V T : X.affineOpens) :
    (pullback (spectrumTripleToScheme f J U V T)).obj (spectrumAmbientSheaf f J M V) ≅
      (pullback (spectrumTripleSecondProjection f J U V T)).obj
        (spectrumSheaf f J M V) :=
  coordinateIso (spectrumTripleSecondProjection f J U V T) (spectrumSpaceMap f J V)
    (spectrumTripleToScheme f J U V T) (spectrumTripleSecondProjection_toScheme f J U V T)
    (spectrumSheaf f J M V)

/-- Recover the third coordinate coefficient sheaf on the triple overlap. -/
def spectrumTripleThirdAmbientCoordinate (U V T : X.affineOpens) :
    (pullback (spectrumTripleToScheme f J U V T)).obj (spectrumAmbientSheaf f J M T) ≅
      (pullback (spectrumTripleThirdProjection f J U V T)).obj
        (spectrumSheaf f J M T) :=
  coordinateIso (spectrumTripleThirdProjection f J U V T) (spectrumSpaceMap f J T)
    (spectrumTripleToScheme f J U V T) (spectrumTripleThirdProjection_toScheme f J U V T)
    (spectrumSheaf f J M T)

end FLT.Mazur.BaseAdicRees
