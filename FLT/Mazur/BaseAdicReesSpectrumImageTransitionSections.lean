/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpectrumAmbientImageIso
public import FLT.Mazur.ModuleSheafLocalEvaluation
public import FLT.Mazur.BaseAdicReesSpectrumTripleAmbientMaps
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

namespace FLT.Mazur.BaseAdicRees

open ModuleSheafMorphismGluing ModuleSheafOpenImmersionLocalHom
open ModuleSheafOverlapImageTransition

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

attribute [local instance] spectrumSpaceMap_isOpenImmersion
attribute [local irreducible] Scheme.Modules.pullback spectrumSheaf
attribute [local irreducible] spectrumOverlapSheafIso spectrumSpaceMap
attribute [local irreducible] spectrumOverlapAmbientSheafIso localHom
attribute [local irreducible] spectrumTripleLastPairProjection spectrumTripleOuterPairProjection

/-- A chart image transition acts by the original ambient comparison. -/
lemma spectrumAmbientChartImageTransition_app (U V : X.affineOpens)
    (W : (relativeSpace f J).Opens)
    (hU : W ≤ spectrumImageOpen f J U) (hV : W ≤ spectrumImageOpen f J V)
    (s : Γ(spectrumAmbientSheaf f J M U, W)) :
    localEval (M := spectrumAmbientSheaf f J M U) (N := spectrumAmbientSheaf f J M V)
      (spectrumAmbientChartImageTransition f J M U V).hom (le_inf hU hV) s =
      localEval (M := spectrumAmbientSheaf f J M U) (N := spectrumAmbientSheaf f J M V)
        (localHom (M := spectrumAmbientSheaf f J M U) (N := spectrumAmbientSheaf f J M V)
          (spectrumOverlapToSpace f J U V) (spectrumOverlapAmbientSheafIso f J M U V).hom)
        ((le_inf hU hV).trans_eq (spectrumOverlapToSpace_opensRange f J U V).symm) s := by
  exact localEval_of_iso_eq
    (M := spectrumAmbientSheaf f J M U)
    (N := spectrumAmbientSheaf f J M V)
    (spectrumOverlapToSpace_opensRange f J U V) _
    (spectrumAmbientChartImageTransition f J M U V)
    (spectrumAmbientChartImageTransition_eq f J M U V) _
    (spectrumAmbientOverlapImageIso_hom f J M U V) W (le_inf hU hV) s

omit [IsLocallyNoetherian X] in
/-- Every common subopen lies in the actual triple image. -/
lemma le_spectrumTripleToScheme_opensRange (U V T : X.affineOpens)
    (W : (relativeSpace f J).Opens)
    (hU : W ≤ spectrumImageOpen f J U) (hV : W ≤ spectrumImageOpen f J V)
    (hT : W ≤ spectrumImageOpen f J T) :
    W ≤ (spectrumTripleToScheme f J U V T).opensRange := by
  rw [show (spectrumTripleToScheme f J U V T).opensRange =
      spectrumImageOpen f J U ⊓ spectrumImageOpen f J V ⊓
        spectrumImageOpen f J T from
    TopologicalSpace.Opens.ext (spectrumTripleToScheme_range f J U V T)]
  exact le_inf (le_inf hU hV) hT

/-- The first pair transition restricts to its normalized triple map. -/
lemma spectrumTripleFirstAmbientMap_app (U V T : X.affineOpens)
    (W : (relativeSpace f J).Opens)
    (hU : W ≤ spectrumImageOpen f J U) (hV : W ≤ spectrumImageOpen f J V)
    (hT : W ≤ spectrumImageOpen f J T)
    (s : Γ(spectrumAmbientSheaf f J M U, W)) :
    localEval (spectrumAmbientChartImageTransition f J M U V).hom (le_inf hU hV) s =
      localEval (localHom
        (M := (pushforward (spectrumSpaceMap f J U)).obj (spectrumSheaf f J M U))
        (N := (pushforward (spectrumSpaceMap f J V)).obj (spectrumSheaf f J M V))
        (spectrumTripleToScheme f J U V T) (spectrumTripleFirstAmbientMap f J M U V T))
          (le_spectrumTripleToScheme_opensRange f J U V T W hU hV hT) s := by
  rw [spectrumAmbientChartImageTransition_app f J M U V W hU hV]
  unfold spectrumTripleFirstAmbientMap spectrumAmbientSheaf
  exact (localEval_normalize
    (M := (pushforward (spectrumSpaceMap f J U)).obj (spectrumSheaf f J M U))
    (N := (pushforward (spectrumSpaceMap f J V)).obj (spectrumSheaf f J M V))
    (spectrumOverlapToSpace f J U V)
    (spectrumTripleFirstPairProjection f J U V T) (spectrumTripleToScheme f J U V T)
    rfl (spectrumOverlapAmbientSheafIso f J M U V).hom W
    (le_spectrumTripleToScheme_opensRange f J U V T W hU hV hT) s).symm

/-- The last pair transition restricts to its normalized triple map. -/
lemma spectrumTripleLastAmbientMap_app (U V T : X.affineOpens)
    (W : (relativeSpace f J).Opens)
    (hU : W ≤ spectrumImageOpen f J U) (hV : W ≤ spectrumImageOpen f J V)
    (hT : W ≤ spectrumImageOpen f J T)
    (s : Γ(spectrumAmbientSheaf f J M V, W)) :
    localEval (spectrumAmbientChartImageTransition f J M V T).hom (le_inf hV hT) s =
      localEval (localHom
        (M := (pushforward (spectrumSpaceMap f J V)).obj (spectrumSheaf f J M V))
        (N := (pushforward (spectrumSpaceMap f J T)).obj (spectrumSheaf f J M T))
        (spectrumTripleToScheme f J U V T) (spectrumTripleLastAmbientMap f J M U V T))
          (le_spectrumTripleToScheme_opensRange f J U V T W hU hV hT) s := by
  rw [spectrumAmbientChartImageTransition_app f J M V T W hV hT]
  unfold spectrumTripleLastAmbientMap spectrumAmbientSheaf
  exact (localEval_normalize
    (M := (pushforward (spectrumSpaceMap f J V)).obj (spectrumSheaf f J M V))
    (N := (pushforward (spectrumSpaceMap f J T)).obj (spectrumSheaf f J M T))
    (spectrumOverlapToSpace f J V T)
    (spectrumTripleLastPairProjection f J U V T) (spectrumTripleToScheme f J U V T)
    (spectrumTripleLastPairProjection_toScheme f J U V T)
    (spectrumOverlapAmbientSheafIso f J M V T).hom
    W
    (le_spectrumTripleToScheme_opensRange f J U V T W hU hV hT) s).symm

/-- The outer pair transition restricts to its normalized triple map. -/
lemma spectrumTripleOuterAmbientMap_app (U V T : X.affineOpens)
    (W : (relativeSpace f J).Opens)
    (hU : W ≤ spectrumImageOpen f J U) (hV : W ≤ spectrumImageOpen f J V)
    (hT : W ≤ spectrumImageOpen f J T)
    (s : Γ(spectrumAmbientSheaf f J M U, W)) :
    localEval (spectrumAmbientChartImageTransition f J M U T).hom (le_inf hU hT) s =
      localEval (localHom
        (M := (pushforward (spectrumSpaceMap f J U)).obj (spectrumSheaf f J M U))
        (N := (pushforward (spectrumSpaceMap f J T)).obj (spectrumSheaf f J M T))
        (spectrumTripleToScheme f J U V T) (spectrumTripleOuterAmbientMap f J M U V T))
          (le_spectrumTripleToScheme_opensRange f J U V T W hU hV hT) s := by
  rw [spectrumAmbientChartImageTransition_app f J M U T W hU hT]
  unfold spectrumTripleOuterAmbientMap spectrumAmbientSheaf
  exact (localEval_normalize
    (M := (pushforward (spectrumSpaceMap f J U)).obj (spectrumSheaf f J M U))
    (N := (pushforward (spectrumSpaceMap f J T)).obj (spectrumSheaf f J M T))
    (spectrumOverlapToSpace f J U T)
    (spectrumTripleOuterPairProjection f J U V T) (spectrumTripleToScheme f J U V T)
    (spectrumTripleOuterPairProjection_toScheme f J U V T)
    (spectrumOverlapAmbientSheafIso f J M U T).hom
    W
    (le_spectrumTripleToScheme_opensRange f J U V T W hU hV hT) s).symm

end FLT.Mazur.BaseAdicRees
