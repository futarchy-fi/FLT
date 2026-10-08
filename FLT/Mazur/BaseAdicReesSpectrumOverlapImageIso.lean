/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpectrumImageTransitionTransport

/-!
# Sealed isomorphisms on actual overlap images

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

/-- The coefficient overlap isomorphism on its actual image, before reindexing. -/
@[irreducible]
def spectrumOverlapSheafImageIso (U V : X.affineOpens) :
    ((pushforward (spectrumSpaceMap f J U)).obj
      (spectrumSheaf f J M U)).over (spectrumOverlapToSpace f J U V).opensRange ≅
    ((pushforward (spectrumSpaceMap f J V)).obj
      (spectrumSheaf f J M V)).over (spectrumOverlapToSpace f J U V).opensRange :=
  imageIso (spectrumSpaceMap f J U) (spectrumSpaceMap f J V)
    (spectrumOverlapFirst f J U V) (spectrumOverlapSecond f J U V)
    (spectrumOverlapToSpace f J U V) rfl (spectrumOverlap_condition f J U V).symm
    (spectrumOverlapSheafIso f J M U V)

/-- The original chart transition reindexes the image overlap isomorphism. -/
lemma spectrumChartTransition_eq_overlapCoefficientImageIso (U V : X.affineOpens) :
    spectrumChartImageTransition f J M U V =
      Eq.mpr (congrArg (fun A ↦
        ((pushforward (spectrumSpaceMap f J U)).obj
          (spectrumSheaf f J M U)).over A ≅
        ((pushforward (spectrumSpaceMap f J V)).obj
          (spectrumSheaf f J M V)).over A)
        (spectrumOverlapToSpace_opensRange f J U V).symm)
        (spectrumOverlapSheafImageIso f J M U V) := by
  unfold spectrumOverlapSheafImageIso
  exact spectrumChartImageTransition_eq f J M U V

/-- The image overlap morphism extends the specified ambient comparison. -/
lemma spectrumOverlapSheafImageIso_hom (U V : X.affineOpens) :
    (spectrumOverlapSheafImageIso f J M U V).hom =
      localHom
        (M := (pushforward (spectrumSpaceMap f J U)).obj (spectrumSheaf f J M U))
        (N := (pushforward (spectrumSpaceMap f J V)).obj (spectrumSheaf f J M V))
        (spectrumOverlapToSpace f J U V) (spectrumOverlapAmbientSheafIso f J M U V).hom := by
  unfold spectrumOverlapSheafImageIso
  rw [imageIso_hom, spectrumOverlapAmbientSheafIso_hom_eq]

end FLT.Mazur.BaseAdicRees
