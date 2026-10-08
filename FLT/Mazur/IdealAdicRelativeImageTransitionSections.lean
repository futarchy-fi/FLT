/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeAmbientImageIso
public import FLT.Mazur.ModuleSheafLocalEvaluation
public import FLT.Mazur.IdealAdicRelativeTripleAmbientMaps
public import FLT.Mazur.ModuleSheafLocalHomNormalization
public import FLT.Mazur.ModuleSheafLocalIsoTransport

/-!
# Sections of image coefficient transitions

The image-open transitions act by the original ambient overlap maps.
Restriction to the triple image agrees with normalized triple pullback.
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
open ModuleSheafOverlapImageTransition

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local instance] relativeTensorChart_isOpenImmersion
attribute [local irreducible] Scheme.Modules.pullback relativeChartCoefficientSheaf
attribute [local irreducible] relativeOverlapCoefficientIso relativeTensorChart
attribute [local irreducible] relativeOverlapAmbientCoefficientIso localHom
attribute [local irreducible] relativeTripleLastPairProjection relativeTripleOuterPairProjection

/-- A chart image transition acts by the original ambient comparison. -/
lemma relativeAmbientChartImageTransition_app (U V : X.affineOpens)
    (W : (relativeScheme J f).Opens)
    (hU : W ≤ relativeTensorImageOpen J f U) (hV : W ≤ relativeTensorImageOpen J f V)
    (s : Γ(relativeAmbientCoefficient J f U, W)) :
    localEval (M := relativeAmbientCoefficient J f U) (N := relativeAmbientCoefficient J f V)
      (relativeAmbientChartImageTransition J f U V).hom (le_inf hU hV) s =
      localEval (M := relativeAmbientCoefficient J f U) (N := relativeAmbientCoefficient J f V)
        (localHom (M := relativeAmbientCoefficient J f U) (N := relativeAmbientCoefficient J f V)
          (relativeOverlapToScheme J f U V) (relativeOverlapAmbientCoefficientIso J f U V).hom)
        ((le_inf hU hV).trans_eq (relativeOverlapToScheme_opensRange J f U V).symm) s := by
  exact localEval_of_iso_eq
    (M := relativeAmbientCoefficient J f U)
    (N := relativeAmbientCoefficient J f V)
    (relativeOverlapToScheme_opensRange J f U V) _
    (relativeAmbientChartImageTransition J f U V)
    (relativeAmbientChartImageTransition_eq J f U V) _
    (relativeAmbientOverlapImageIso_hom J f U V) W (le_inf hU hV) s

omit [IsLocallyNoetherian X] [IsAffine Y] in
/-- Every common subopen lies in the actual triple image. -/
lemma le_relativeTripleToScheme_opensRange (U V T : X.affineOpens)
    (W : (relativeScheme J f).Opens)
    (hU : W ≤ relativeTensorImageOpen J f U) (hV : W ≤ relativeTensorImageOpen J f V)
    (hT : W ≤ relativeTensorImageOpen J f T) :
    W ≤ (relativeTripleToScheme J f U V T).opensRange := by
  rw [show (relativeTripleToScheme J f U V T).opensRange =
      relativeTensorImageOpen J f U ⊓ relativeTensorImageOpen J f V ⊓
        relativeTensorImageOpen J f T from
    TopologicalSpace.Opens.ext (relativeTripleToScheme_range J f U V T)]
  exact le_inf (le_inf hU hV) hT

/-- The first pair transition restricts to its normalized triple map. -/
lemma relativeTripleFirstAmbientMap_app (U V T : X.affineOpens)
    (W : (relativeScheme J f).Opens)
    (hU : W ≤ relativeTensorImageOpen J f U) (hV : W ≤ relativeTensorImageOpen J f V)
    (hT : W ≤ relativeTensorImageOpen J f T)
    (s : Γ(relativeAmbientCoefficient J f U, W)) :
    localEval (relativeAmbientChartImageTransition J f U V).hom (le_inf hU hV) s =
      localEval (localHom
        (M := (pushforward (relativeTensorChart J f U)).obj (relativeChartCoefficientSheaf J f U))
        (N := (pushforward (relativeTensorChart J f V)).obj (relativeChartCoefficientSheaf J f V))
        (relativeTripleToScheme J f U V T) (relativeTripleFirstAmbientMap J f U V T))
          (le_relativeTripleToScheme_opensRange J f U V T W hU hV hT) s := by
  rw [relativeAmbientChartImageTransition_app J f U V W hU hV]
  unfold relativeTripleFirstAmbientMap relativeAmbientCoefficient
  exact (localEval_normalize
    (M := (pushforward (relativeTensorChart J f U)).obj (relativeChartCoefficientSheaf J f U))
    (N := (pushforward (relativeTensorChart J f V)).obj (relativeChartCoefficientSheaf J f V))
    (relativeOverlapToScheme J f U V)
    (relativeTripleFirstPairProjection J f U V T) (relativeTripleToScheme J f U V T)
    rfl (relativeOverlapAmbientCoefficientIso J f U V).hom W
    (le_relativeTripleToScheme_opensRange J f U V T W hU hV hT) s).symm

/-- The last pair transition restricts to its normalized triple map. -/
lemma relativeTripleLastAmbientMap_app (U V T : X.affineOpens)
    (W : (relativeScheme J f).Opens)
    (hU : W ≤ relativeTensorImageOpen J f U) (hV : W ≤ relativeTensorImageOpen J f V)
    (hT : W ≤ relativeTensorImageOpen J f T)
    (s : Γ(relativeAmbientCoefficient J f V, W)) :
    localEval (relativeAmbientChartImageTransition J f V T).hom (le_inf hV hT) s =
      localEval (localHom
        (M := (pushforward (relativeTensorChart J f V)).obj (relativeChartCoefficientSheaf J f V))
        (N := (pushforward (relativeTensorChart J f T)).obj (relativeChartCoefficientSheaf J f T))
        (relativeTripleToScheme J f U V T) (relativeTripleLastAmbientMap J f U V T))
          (le_relativeTripleToScheme_opensRange J f U V T W hU hV hT) s := by
  rw [relativeAmbientChartImageTransition_app J f V T W hV hT]
  unfold relativeTripleLastAmbientMap relativeAmbientCoefficient
  exact (localEval_normalize
    (M := (pushforward (relativeTensorChart J f V)).obj (relativeChartCoefficientSheaf J f V))
    (N := (pushforward (relativeTensorChart J f T)).obj (relativeChartCoefficientSheaf J f T))
    (relativeOverlapToScheme J f V T)
    (relativeTripleLastPairProjection J f U V T) (relativeTripleToScheme J f U V T)
    (relativeTripleLastPairProjection_toScheme J f U V T)
    (relativeOverlapAmbientCoefficientIso J f V T).hom
    W
    (le_relativeTripleToScheme_opensRange J f U V T W hU hV hT) s).symm

/-- The outer pair transition restricts to its normalized triple map. -/
lemma relativeTripleOuterAmbientMap_app (U V T : X.affineOpens)
    (W : (relativeScheme J f).Opens)
    (hU : W ≤ relativeTensorImageOpen J f U) (hV : W ≤ relativeTensorImageOpen J f V)
    (hT : W ≤ relativeTensorImageOpen J f T)
    (s : Γ(relativeAmbientCoefficient J f U, W)) :
    localEval (relativeAmbientChartImageTransition J f U T).hom (le_inf hU hT) s =
      localEval (localHom
        (M := (pushforward (relativeTensorChart J f U)).obj (relativeChartCoefficientSheaf J f U))
        (N := (pushforward (relativeTensorChart J f T)).obj (relativeChartCoefficientSheaf J f T))
        (relativeTripleToScheme J f U V T) (relativeTripleOuterAmbientMap J f U V T))
          (le_relativeTripleToScheme_opensRange J f U V T W hU hV hT) s := by
  rw [relativeAmbientChartImageTransition_app J f U T W hU hT]
  unfold relativeTripleOuterAmbientMap relativeAmbientCoefficient
  exact (localEval_normalize
    (M := (pushforward (relativeTensorChart J f U)).obj (relativeChartCoefficientSheaf J f U))
    (N := (pushforward (relativeTensorChart J f T)).obj (relativeChartCoefficientSheaf J f T))
    (relativeOverlapToScheme J f U T)
    (relativeTripleOuterPairProjection J f U V T) (relativeTripleToScheme J f U V T)
    (relativeTripleOuterPairProjection_toScheme J f U V T)
    (relativeOverlapAmbientCoefficientIso J f U T).hom
    W
    (le_relativeTripleToScheme_opensRange J f U V T W hU hV hT) s).symm

end FLT.Mazur.IdealAdicGradedPullback
