/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelChartNaturality

/-!
# Original power-section naturality of the actual direct image

The chosen identification of the actual pushforward with all original ideal
power sections commutes with every original affine restriction, degree by degree.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.BaseAdicThickening

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

attribute [local irreducible] modelPushforwardChartSectionsIso modelSheafTopCoefficientsEquiv
attribute [local irreducible] modelTransitionSections

/-- The actual affine pushforward power coordinates commute with original restrictions. -/
lemma modelPushforwardPowerSectionsIso_naturality {U V : X.affineOpens} (h : U.1 ≤ V.1)
    (s : Γ(modelPushforward f J M, V.1)) :
    (modelPushforwardPowerSectionsIso f J M U).hom
        ((modelPushforward f J M).presheaf.map (homOfLE h).op s) =
      IdealPowerRees.chartRestriction ((baseIdeal R J).comap f) M V h le_rfl
        (homOfLE h) ((modelPushforwardPowerSectionsIso f J M V).hom s) := by
  have hh := congrArg (fun k ↦ k s) (modelPushforwardChartSectionsIso_naturality f J M h)
  change (modelPushforwardChartSectionsIso f J M U).hom
      ((modelPushforward f J M).presheaf.map (homOfLE h).op s) =
    modelTransitionSections f J M h ((modelPushforwardChartSectionsIso f J M V).hom s) at hh
  change nativePowerSectionsEquiv f J M U
      (modelSheafTopCoefficientsEquiv f J M U
        ((modelPushforwardChartSectionsIso f J M U).hom
          ((modelPushforward f J M).presheaf.map (homOfLE h).op s))) = _
  rw [hh]
  exact modelTransitionSections_powerSections f J M h _

/-- Every degree restricts by the actual original ideal-power sheaf map. -/
lemma modelPushforwardPowerSectionsIso_naturality_apply {U V : X.affineOpens}
    (h : U.1 ≤ V.1) (s : Γ(modelPushforward f J M, V.1)) (n : ℕ) :
    (modelPushforwardPowerSectionsIso f J M U).hom
        ((modelPushforward f J M).presheaf.map (homOfLE h).op s) n =
      (GlobalIdealPower.multiple (((baseIdeal R J).comap f) ^ n) M).presheaf.map
        (homOfLE h).op ((modelPushforwardPowerSectionsIso f J M V).hom s n) := by
  rw [modelPushforwardPowerSectionsIso_naturality]
  rfl

end FLT.Mazur.BaseAdicRees
