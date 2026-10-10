/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeCoefficientProjection
public import FLT.Mazur.ModuleSheafLocalEquation

/-!
# The descended projections on genuine overlap pullbacks

The image transition equation implies the corresponding equation on the
actual scheme overlap, with the original ambient coefficient comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

open ModuleSheafMorphismGluing ModuleSheafOpenImmersionLocalHom

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local irreducible] Scheme.Modules.pullback relativeChartCoefficientSheaf
attribute [local irreducible] relativeOverlapAmbientCoefficientIso localHom

/-- The sealed original image transition intertwines the actual descended projections. -/
lemma relativeDescendedCoefficientProjection_image_eval (U V : X.affineOpens)
    (W : (relativeScheme J f).Opens)
    (hU : W ≤ relativeTensorImageOpen J f U) (hV : W ≤ relativeTensorImageOpen J f V)
    (s : Γ(relativeDescendedCoefficientSheaf J f, W)) :
    localEval (relativeAmbientChartImageTransition J f U V).hom (le_inf hU hV)
        ((relativeDescendedCoefficientProjection J f U).app W s) =
      (relativeDescendedCoefficientProjection J f V).app W s := by
  unfold relativeAmbientChartImageTransition
  exact localEval_projection _ _ _
    (relativeDescendedCoefficientProjection_transition J f U V) (le_inf hU hV) s

/-- On the actual overlap image, the projections obey the genuine ambient comparison. -/
lemma relativeDescendedCoefficientProjection_overlap_eval (U V : X.affineOpens)
    (W : (relativeScheme J f).Opens) (hW : W ≤ (relativeOverlapToScheme J f U V).opensRange)
    (s : Γ(relativeDescendedCoefficientSheaf J f, W)) :
    localEval (localHom (relativeOverlapToScheme J f U V)
        (relativeOverlapAmbientCoefficientIso J f U V).hom) hW
        ((relativeDescendedCoefficientProjection J f U).app W s) =
      (relativeDescendedCoefficientProjection J f V).app W s := by
  have hUV := hW.trans_eq (relativeOverlapToScheme_opensRange J f U V)
  have h := relativeAmbientChartImageTransition_app J f U V W
    (hUV.trans inf_le_left) (hUV.trans inf_le_right)
    ((relativeDescendedCoefficientProjection J f U).app W s)
  exact h.symm.trans (relativeDescendedCoefficientProjection_image_eval J f U V W
    (hUV.trans inf_le_left) (hUV.trans inf_le_right) s)

/-- Pullbacks of the canonical projections retain the original ambient overlap isomorphism. -/
lemma relativeDescendedCoefficientProjection_overlap (U V : X.affineOpens) :
    (pullback (relativeOverlapToScheme J f U V)).map
        (relativeDescendedCoefficientProjection J f U) ≫
        (relativeOverlapAmbientCoefficientIso J f U V).hom =
      (pullback (relativeOverlapToScheme J f U V)).map
        (relativeDescendedCoefficientProjection J f V) :=
  pullback_projection_of_localEval (relativeOverlapToScheme J f U V) _ _ _
    (relativeDescendedCoefficientProjection_overlap_eval J f U V)

end FLT.Mazur.IdealAdicGradedPullback
