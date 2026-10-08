/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpectrumImageTransitionSections
public import FLT.Mazur.BaseAdicReesSpectrumTripleAmbientCocycle

/-!
# The image-open coefficient cocycle

The actual transitions on the image cover satisfy the sectionwise cocycle
required for gluing module sheaves, including their pushforward comparisons.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.BaseAdicRees

open ModuleSheafMorphismGluing

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

attribute [local irreducible] Scheme.Modules.pullback spectrumSheaf
attribute [local irreducible] spectrumOverlapSheafIso spectrumImageSheafPushforwardIso

/-- Sealed section evaluation transfers the ambient morphism cocycle. -/
lemma spectrumTripleAmbientMap_cocycle_eval (U V T : X.affineOpens)
    (W : (relativeSpace f J).Opens) (hW : W ≤ (spectrumTripleToScheme f J U V T).opensRange)
    (s : Γ(spectrumAmbientSheaf f J M U, W)) :
    localEval (ModuleSheafOpenImmersionLocalHom.localHom (spectrumTripleToScheme f J U V T)
      (spectrumTripleLastAmbientMap f J M U V T)) hW
      (localEval (ModuleSheafOpenImmersionLocalHom.localHom (spectrumTripleToScheme f J U V T)
        (spectrumTripleFirstAmbientMap f J M U V T)) hW s) =
      localEval (ModuleSheafOpenImmersionLocalHom.localHom (spectrumTripleToScheme f J U V T)
        (spectrumTripleOuterAmbientMap f J M U V T)) hW s := by
  have h := congrArg (ModuleSheafOpenImmersionLocalHom.localHom (spectrumTripleToScheme f J U V T))
    (spectrumTripleAmbientMap_cocycle f J M U V T)
  rw [ModuleSheafOpenImmersionLocalHom.localHom_comp] at h
  have hs := congrArg (fun a ↦ localEval a hW s) h
  rw [localEval_comp] at hs
  exact hs

/-- Chart pushforward transitions compose on every subopen of a triple intersection. -/
theorem spectrumAmbientChartImageTransition_cocycle (U V T : X.affineOpens)
    (W : (relativeSpace f J).Opens)
    (hU : W ≤ spectrumImageOpen f J U) (hV : W ≤ spectrumImageOpen f J V)
    (hT : W ≤ spectrumImageOpen f J T) (s : Γ(spectrumAmbientSheaf f J M U, W)) :
    localEval (spectrumAmbientChartImageTransition f J M V T).hom (le_inf hV hT)
      (localEval (spectrumAmbientChartImageTransition f J M U V).hom (le_inf hU hV) s) =
        localEval (spectrumAmbientChartImageTransition f J M U T).hom (le_inf hU hT) s := by
  rw [spectrumTripleLastAmbientMap_app f J M U V T W hU hV hT,
    spectrumTripleFirstAmbientMap_app f J M U V T W hU hV hT,
    spectrumTripleOuterAmbientMap_app f J M U V T W hU hV hT]
  exact spectrumTripleAmbientMap_cocycle_eval f J M U V T W _ s

/-- Image-object transitions act by conjugating the chart transition on sections. -/
lemma spectrumImageSheafTransition_app (U V : X.affineOpens)
    (W : (relativeSpace f J).Opens)
    (hU : W ≤ spectrumImageOpen f J U) (hV : W ≤ spectrumImageOpen f J V)
    (s : Γ((pushforward (spectrumImageOpen f J U).ι).obj
      (spectrumImageSheaf f J M U), W)) :
    localEval (spectrumImageSheafTransition f J M U V).hom (le_inf hU hV) s =
      (spectrumImageSheafPushforwardIso f J M V).inv.app W
        (localEval (spectrumAmbientChartImageTransition f J M U V).hom (le_inf hU hV)
          ((spectrumImageSheafPushforwardIso f J M U).hom.app W s)) := by
  unfold spectrumImageSheafTransition spectrumAmbientChartImageTransition
  exact localEval_conjugate _ _ _ _ _ _ _

/-- The actual image coefficient transitions satisfy the module-sheaf gluing cocycle. -/
theorem spectrumImageSheafTransition_cocycle (U V T : X.affineOpens)
    (W : (relativeSpace f J).Opens)
    (hU : W ≤ spectrumImageOpen f J U) (hV : W ≤ spectrumImageOpen f J V)
    (hT : W ≤ spectrumImageOpen f J T)
    (s : Γ((pushforward (spectrumImageOpen f J U).ι).obj
      (spectrumImageSheaf f J M U), W)) :
    localEval (spectrumImageSheafTransition f J M V T).hom (le_inf hV hT)
      (localEval (spectrumImageSheafTransition f J M U V).hom (le_inf hU hV) s) =
        localEval (spectrumImageSheafTransition f J M U T).hom (le_inf hU hT) s := by
  have hc (t : Γ(spectrumAmbientSheaf f J M V, W)) :
      (spectrumImageSheafPushforwardIso f J M V).hom.app W
        ((spectrumImageSheafPushforwardIso f J M V).inv.app W t) = t :=
    ConcreteCategory.congr_hom
      (congrArg (fun a ↦ a.app W) (spectrumImageSheafPushforwardIso f J M V).inv_hom_id) t
  rw [spectrumImageSheafTransition_app f J M V T W hV hT,
    spectrumImageSheafTransition_app f J M U V W hU hV,
    spectrumImageSheafTransition_app f J M U T W hU hT, hc,
    spectrumAmbientChartImageTransition_cocycle f J M U V T W hU hV hT]

end FLT.Mazur.BaseAdicRees
