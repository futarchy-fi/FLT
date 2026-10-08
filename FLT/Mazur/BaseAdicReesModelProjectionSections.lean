/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelPushforward
public import FLT.Mazur.BaseAdicReesModelProjectionCompatibility
public import FLT.Mazur.ModuleSheafProjectionSections

/-!
# Original pushforward chart sections as descended projections

The chosen pushforward section isomorphism is the actual descended projection,
evaluated on the original source preimage and transported to the whole chart.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (J : Ideal R)

attribute [local instance] spectrumSpaceMap_isOpenImmersion
attribute [local semireducible] modelSpectrum
attribute [local irreducible] chartSpaceMap modelSheaf

/-- The original projection preimage is exactly the whole spectrum chart image. -/
lemma spectrumSpaceMap_image_top (V : X.affineOpens) :
    spectrumSpaceMap f J V ''ᵁ ⊤ = modelSourceProjection f J ⁻¹ᵁ V.1 :=
  (chartSpaceMap f J V).image_top_eq_opensRange.trans (chartSpaceMap_opensRange f J V)

/-- Pulling the original source preimage back to its spectrum chart gives the whole chart. -/
lemma spectrumSpaceMap_preimage_source (V : X.affineOpens) :
    spectrumSpaceMap f J V ⁻¹ᵁ (modelSourceProjection f J ⁻¹ᵁ V.1) = ⊤ := by
  rw [← spectrumSpaceMap_image_top]
  exact (spectrumSpaceMap f J V).preimage_image_eq ⊤

variable [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

attribute [local irreducible] spectrumDescendedSheaf spectrumDescendedSheafProjection
attribute [local irreducible] spectrumDescendedSheafChartIso

/-- The actual pushforward chart isomorphism retains the original descended projection. -/
lemma modelPushforwardChartSectionsIso_projection (V : X.affineOpens) :
    (modelPushforwardChartSectionsIso f J M V).hom =
      ModuleSheafProjectionSections.sections (spectrumSpaceMap f J V)
        (spectrumDescendedSheaf f J M) (spectrumSheaf f J M V)
        (spectrumDescendedSheafProjection f J M V)
        (modelSourceProjection f J ⁻¹ᵁ V.1) ⊤ (spectrumSpaceMap_preimage_source f J V) := by
  exact ModuleSheafProjectionSections.recovery_sections (spectrumSpaceMap f J V)
    (spectrumDescendedSheaf f J M) (spectrumSheaf f J M V)
    (spectrumDescendedSheafProjection f J M V) (spectrumDescendedSheafChartIso f J M V).hom
    (spectrumDescendedSheafChartIso_projection f J M V) ⊤
    (modelSourceProjection f J ⁻¹ᵁ V.1) (spectrumSpaceMap_image_top f J V)

end FLT.Mazur.BaseAdicRees
