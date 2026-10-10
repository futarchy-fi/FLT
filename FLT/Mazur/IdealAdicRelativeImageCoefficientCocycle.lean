/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeImageTransitionSections
public import FLT.Mazur.IdealAdicRelativeTripleAmbientCocycle

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

namespace FLT.Mazur.IdealAdicGradedPullback

open ModuleSheafMorphismGluing

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local irreducible] Scheme.Modules.pullback relativeChartCoefficientSheaf
attribute [local irreducible] relativeOverlapCoefficientIso relativeImageCoefficientPushforwardIso

/-- Sealed section evaluation transfers the ambient morphism cocycle. -/
lemma relativeTripleAmbientMap_cocycle_eval (U V T : X.affineOpens)
    (W : (relativeScheme J f).Opens) (hW : W ≤ (relativeTripleToScheme J f U V T).opensRange)
    (s : Γ(relativeAmbientCoefficient J f U, W)) :
    localEval (ModuleSheafOpenImmersionLocalHom.localHom (relativeTripleToScheme J f U V T)
      (relativeTripleLastAmbientMap J f U V T)) hW
      (localEval (ModuleSheafOpenImmersionLocalHom.localHom (relativeTripleToScheme J f U V T)
        (relativeTripleFirstAmbientMap J f U V T)) hW s) =
      localEval (ModuleSheafOpenImmersionLocalHom.localHom (relativeTripleToScheme J f U V T)
        (relativeTripleOuterAmbientMap J f U V T)) hW s := by
  have h := congrArg (ModuleSheafOpenImmersionLocalHom.localHom (relativeTripleToScheme J f U V T))
    (relativeTripleAmbientMap_cocycle J f U V T)
  rw [ModuleSheafOpenImmersionLocalHom.localHom_comp] at h
  have hs := congrArg (fun a ↦ localEval a hW s) h
  rw [localEval_comp] at hs
  exact hs

/-- Chart pushforward transitions compose on every subopen of a triple intersection. -/
theorem relativeAmbientChartImageTransition_cocycle (U V T : X.affineOpens)
    (W : (relativeScheme J f).Opens)
    (hU : W ≤ relativeTensorImageOpen J f U) (hV : W ≤ relativeTensorImageOpen J f V)
    (hT : W ≤ relativeTensorImageOpen J f T) (s : Γ(relativeAmbientCoefficient J f U, W)) :
    localEval (relativeAmbientChartImageTransition J f V T).hom (le_inf hV hT)
      (localEval (relativeAmbientChartImageTransition J f U V).hom (le_inf hU hV) s) =
        localEval (relativeAmbientChartImageTransition J f U T).hom (le_inf hU hT) s := by
  rw [relativeTripleLastAmbientMap_app J f U V T W hU hV hT,
    relativeTripleFirstAmbientMap_app J f U V T W hU hV hT,
    relativeTripleOuterAmbientMap_app J f U V T W hU hV hT]
  exact relativeTripleAmbientMap_cocycle_eval J f U V T W _ s

/-- Image-object transitions act by conjugating the chart transition on sections. -/
lemma relativeImageCoefficientTransition_app (U V : X.affineOpens)
    (W : (relativeScheme J f).Opens)
    (hU : W ≤ relativeTensorImageOpen J f U) (hV : W ≤ relativeTensorImageOpen J f V)
    (s : Γ((pushforward (relativeTensorImageOpen J f U).ι).obj
      (relativeImageCoefficientSheaf J f U), W)) :
    localEval (relativeImageCoefficientTransition J f U V).hom (le_inf hU hV) s =
      (relativeImageCoefficientPushforwardIso J f V).inv.app W
        (localEval (relativeAmbientChartImageTransition J f U V).hom (le_inf hU hV)
          ((relativeImageCoefficientPushforwardIso J f U).hom.app W s)) := by
  unfold relativeImageCoefficientTransition relativeAmbientChartImageTransition
  exact localEval_conjugate _ _ _ _ _ _ _

/-- The actual image coefficient transitions satisfy the module-sheaf gluing cocycle. -/
theorem relativeImageCoefficientTransition_cocycle (U V T : X.affineOpens)
    (W : (relativeScheme J f).Opens)
    (hU : W ≤ relativeTensorImageOpen J f U) (hV : W ≤ relativeTensorImageOpen J f V)
    (hT : W ≤ relativeTensorImageOpen J f T)
    (s : Γ((pushforward (relativeTensorImageOpen J f U).ι).obj
      (relativeImageCoefficientSheaf J f U), W)) :
    localEval (relativeImageCoefficientTransition J f V T).hom (le_inf hV hT)
      (localEval (relativeImageCoefficientTransition J f U V).hom (le_inf hU hV) s) =
        localEval (relativeImageCoefficientTransition J f U T).hom (le_inf hU hT) s := by
  have hc (t : Γ(relativeAmbientCoefficient J f V, W)) :
      (relativeImageCoefficientPushforwardIso J f V).hom.app W
        ((relativeImageCoefficientPushforwardIso J f V).inv.app W t) = t :=
    ConcreteCategory.congr_hom
      (congrArg (fun a ↦ a.app W) (relativeImageCoefficientPushforwardIso J f V).inv_hom_id) t
  rw [relativeImageCoefficientTransition_app J f V T W hV hT,
    relativeImageCoefficientTransition_app J f U V W hU hV,
    relativeImageCoefficientTransition_app J f U T W hU hT, hc,
    relativeAmbientChartImageTransition_cocycle J f U V T W hU hV hT]

end FLT.Mazur.IdealAdicGradedPullback
