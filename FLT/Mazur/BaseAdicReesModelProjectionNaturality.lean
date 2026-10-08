/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelRestrictionRecovery
public import FLT.Mazur.ModuleSheafAdjointPathNaturality

/-!
# Original restriction equations for descended Rees projections

The actual descended projections commute with the original coefficient
restriction after its pullback unit. Both the scheme maps and the chosen
chart recovery isomorphisms are retained in this adjoint equation.
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

attribute [local instance] spectrumSpaceMap_isOpenImmersion
attribute [local irreducible] Scheme.Modules.pullback spectrumSheaf spectrumSpaceMap

/-- The adjoint of the chosen chart recovery is its original descended projection. -/
lemma spectrumModelChartRecovery_adjoint (U : X.affineOpens) :
    (pullbackPushforwardAdjunction (spectrumSpaceMap f J U)).unit.app
        (spectrumDescendedSheaf f J M) ≫
      (pushforward (spectrumSpaceMap f J U)).map (spectrumModelChartRecovery f J M U).hom =
        spectrumDescendedSheafProjection f J M U :=
  ModuleSheafAdjointPathNaturality.projection_of_openCounit (spectrumSpaceMap f J U)
    (spectrumDescendedSheaf f J M) (spectrumSheaf f J M U)
    (spectrumDescendedSheafProjection f J M U) (spectrumModelChartRecovery f J M U).hom
    (spectrumModelChartRecovery_projection f J M U)

/-- Actual descended projections commute with the original nested coefficient restriction. -/
lemma spectrumDescendedSheafProjection_restriction {U V : X.affineOpens}
    (h : U.1 ≤ V.1) :
    spectrumDescendedSheafProjection f J M V ≫
      (pushforward (spectrumSpaceMap f J V)).map
        ((pullbackPushforwardAdjunction (spectrumMap f J h)).unit.app
          (spectrumSheaf f J M V)) ≫
      (pushforward (spectrumSpaceMap f J V)).map
        ((pushforward (spectrumMap f J h)).map (spectrumRestriction f J M h)) ≫
      (pushforwardComp (spectrumMap f J h) (spectrumSpaceMap f J V)).hom.app
        (spectrumSheaf f J M U) ≫
      (pushforwardCongr (spectrumMap_chart f J h)).hom.app (spectrumSheaf f J M U) =
        spectrumDescendedSheafProjection f J M U :=
  ModuleSheafAdjointPathNaturality.projection_comp (spectrumMap f J h)
    (spectrumSpaceMap f J V) (spectrumSpaceMap f J U) (spectrumMap_chart f J h)
    (spectrumDescendedSheaf f J M) (spectrumSheaf f J M V) (spectrumSheaf f J M U)
    (spectrumModelChartRecovery f J M V).hom (spectrumModelChartRecovery f J M U).hom
    (spectrumRestriction f J M h) (spectrumDescendedSheafProjection f J M V)
    (spectrumDescendedSheafProjection f J M U)
    (spectrumModelChartRecovery_adjoint f J M V) (spectrumModelChartRecovery_adjoint f J M U)
    (spectrumModelChartRecovery_naturality f J M h)

end FLT.Mazur.BaseAdicRees
