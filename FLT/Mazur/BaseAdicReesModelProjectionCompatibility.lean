/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelDescent
public import FLT.Mazur.ModuleSheafImageIsoProjectionRecovery
public import FLT.Mazur.ModuleSheafLocalEquation

/-!
# Original chart projections of the descended Rees model

The actual descended projections obey the original ambient transitions.
The chart recovery isomorphism is the restriction adjoint of its projection,
so its section formulas can be compared without unfolding the glued families.
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
attribute [local irreducible] Scheme.Modules.pullback spectrumSheaf
attribute [local irreducible] spectrumImageSheaf spectrumChartImageTransition

/-- Descended projections retain the original ambient chart transition. -/
@[reassoc]
lemma spectrumDescendedSheafProjection_transition (U V : X.affineOpens) :
    (spectrumDescendedSheafProjection f J M U).over
        (spectrumImageOpen f J U ⊓ spectrumImageOpen f J V) ≫
      (spectrumChartImageTransition f J M U V).hom =
        (spectrumDescendedSheafProjection f J M V).over
          (spectrumImageOpen f J U ⊓ spectrumImageOpen f J V) := by
  let D := spectrumSheafGluingData f J M
  let F := SheafOfModules.overFunctor (relativeSpace f J).ringCatSheaf
    (spectrumImageOpen f J U ⊓ spectrumImageOpen f J V)
  have h := D.projection_transition U V
  change F.map (D.projection U) ≫
    (F.map (spectrumImageSheafPushforwardIso f J M U).hom ≫
      (spectrumChartImageTransition f J M U V).hom ≫
        F.map (spectrumImageSheafPushforwardIso f J M V).inv) =
          F.map (D.projection V) at h
  have h' := congrArg (fun a ↦ a ≫ F.map (spectrumImageSheafPushforwardIso f J M V).hom) h
  simp only [Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id] at h'
  rw [Category.comp_id] at h'
  change F.map (D.projection U ≫ (spectrumImageSheafPushforwardIso f J M U).hom) ≫ _ =
    F.map (D.projection V ≫ (spectrumImageSheafPushforwardIso f J M V).hom)
  simpa only [F.map_comp, Category.assoc] using h'

/-- On every common subopen the actual projections recover the original section transition. -/
lemma spectrumDescendedSheafProjection_transition_app (U V : X.affineOpens)
    (W : (relativeSpace f J).Opens)
    (hU : W ≤ spectrumImageOpen f J U) (hV : W ≤ spectrumImageOpen f J V)
    (s : Γ(spectrumDescendedSheaf f J M, W)) :
    ModuleSheafMorphismGluing.localEval (spectrumChartImageTransition f J M U V).hom
        (le_inf hU hV) ((spectrumDescendedSheafProjection f J M U).app W s) =
      (spectrumDescendedSheafProjection f J M V).app W s :=
  ModuleSheafMorphismGluing.localEval_projection _ _ _
    (spectrumDescendedSheafProjection_transition f J M U V) _ s

attribute [local semireducible] spectrumImageSheaf

/-- The original chart isomorphism is the restriction adjoint of the actual projection. -/
lemma spectrumDescendedSheafChartIso_projection (U : X.affineOpens) :
    (spectrumDescendedSheafChartIso f J M U).hom =
      (restrictFunctor (spectrumSpaceMap f J U)).map
          (spectrumDescendedSheafProjection f J M U) ≫
        (restrictFunctorAdjCounitIso (spectrumSpaceMap f J U)).hom.app
          (spectrumSheaf f J M U) := by
  unfold spectrumDescendedSheafChartIso spectrumDescendedSheafProjection
    spectrumImageSheafRestrictionIso spectrumImageSheafPushforwardIso
  exact ModuleSheafImageIsoProjectionRecovery.recovery_projection
    (spectrumSpaceMap f J U) (spectrumSheaf f J M U) (spectrumDescendedSheaf f J M)
    (spectrumImageOpen f J U) (spectrumImageIso f J U) (spectrumImageIso_hom_ι f J U)
    ((spectrumSheafGluingData f J M).projection U)
    (spectrumDescendedSheafRestrictionIso f J M U) rfl

end FLT.Mazur.BaseAdicRees
