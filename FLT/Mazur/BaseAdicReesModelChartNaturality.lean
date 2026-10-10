/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelProjectionSections
public import FLT.Mazur.BaseAdicReesModelProjectionNaturality
public import FLT.Mazur.BaseAdicReesModelTransitionSections
public import FLT.Mazur.ModuleSheafProjectionTopNaturality

/-!
# Naturality of the actual pushforward chart sections

The chosen chart sections of the actual direct image restrict by the original
model transition, including its pullback unit and all source preimage transports.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

attribute [local semireducible] modelSpectrum spectrumRestriction
attribute [local irreducible] modelSheaf modelRestriction modelMap chartSpaceMap
attribute [local irreducible] spectrumDescendedSheaf spectrumDescendedSheafProjection
attribute [local irreducible] Scheme.Modules.pullback

/-- Original pushforward chart coordinates commute with the actual model transition. -/
lemma modelPushforwardChartSectionsIso_naturality {U V : X.affineOpens}
    (h : U.1 ≤ V.1) :
    (modelPushforward f J M).presheaf.map (homOfLE h).op ≫
        (modelPushforwardChartSectionsIso f J M U).hom =
      (modelPushforwardChartSectionsIso f J M V).hom ≫
        AddCommGrpCat.ofHom (modelTransitionSections f J M h) := by
  rw [modelPushforwardChartSectionsIso_projection, modelPushforwardChartSectionsIso_projection]
  apply ModuleSheafProjectionSections.sections_naturality_top
    (spectrumMap f J h) (spectrumSpaceMap f J V) (spectrumSpaceMap f J U)
    (spectrumMap_chart f J h) (spectrumDescendedSheaf f J M)
    (spectrumSheaf f J M V) (spectrumSheaf f J M U)
    (spectrumDescendedSheafProjection f J M V) (spectrumDescendedSheafProjection f J M U)
    ((pullbackPushforwardAdjunction (spectrumMap f J h)).unit.app (spectrumSheaf f J M V) ≫
      (pushforward (spectrumMap f J h)).map (spectrumRestriction f J M h))
    _ (homOfLE ((modelSourceProjection f J).preimage_mono h))
    (spectrumSpaceMap_preimage_source f J V) (spectrumSpaceMap_preimage_source f J U)
  simpa only [Functor.map_comp, Category.assoc] using
    spectrumDescendedSheafProjection_restriction f J M h

end FLT.Mazur.BaseAdicRees
