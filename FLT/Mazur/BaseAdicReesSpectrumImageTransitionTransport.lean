/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpectrumAmbientSheaf

/-!
# Equality transport for image coefficient transitions

General image-open maps retain their section maps under equality transport.
The concrete chart transitions have explicit transport and coordinate formulas.
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

omit [IsLocallyNoetherian X] in
/-- The pair image intersection is exactly the overlap immersion's image. -/
lemma spectrumOverlapToSpace_opensRange (U V : X.affineOpens) :
    (spectrumOverlapToSpace f J U V).opensRange =
      spectrumImageOpen f J U ⊓ spectrumImageOpen f J V :=
  TopologicalSpace.Opens.ext (spectrumOverlapToSpace_range f J U V)

/-- The chart transition is precisely equality transport of the overlap image isomorphism. -/
lemma spectrumChartImageTransition_eq (U V : X.affineOpens) :
    spectrumChartImageTransition f J M U V =
      Eq.mpr (congrArg (fun A ↦
        ((pushforward (spectrumSpaceMap f J U)).obj
          (spectrumSheaf f J M U)).over A ≅
        ((pushforward (spectrumSpaceMap f J V)).obj
          (spectrumSheaf f J M V)).over A)
        (spectrumOverlapToSpace_opensRange f J U V).symm)
        (imageIso (spectrumSpaceMap f J U) (spectrumSpaceMap f J V)
          (spectrumOverlapFirst f J U V) (spectrumOverlapSecond f J U V)
          (spectrumOverlapToSpace f J U V) rfl (spectrumOverlap_condition f J U V).symm
          (spectrumOverlapSheafIso f J M U V)) := rfl

/-- The ambient overlap isomorphism has its specified conjugated coordinate map. -/
lemma spectrumOverlapAmbientSheafIso_hom_eq (U V : X.affineOpens) :
    (spectrumOverlapAmbientSheafIso f J M U V).hom =
      (ambientIso (spectrumSpaceMap f J U) (spectrumSpaceMap f J V)
        (spectrumOverlapFirst f J U V) (spectrumOverlapSecond f J U V)
        (spectrumOverlapToSpace f J U V) rfl (spectrumOverlap_condition f J U V).symm
        (spectrumOverlapSheafIso f J M U V)).hom := by
  unfold spectrumOverlapAmbientSheafIso
  rfl

end FLT.Mazur.BaseAdicRees
