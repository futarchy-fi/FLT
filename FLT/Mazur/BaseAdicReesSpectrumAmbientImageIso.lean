/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpectrumOverlapImageIso

/-!
# Ambient module types for image transitions

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

/-- The overlap image comparison with its named ambient module types. -/
@[irreducible]
def spectrumAmbientOverlapImageIso (U V : X.affineOpens) :
    (spectrumAmbientSheaf f J M U).over (spectrumOverlapToSpace f J U V).opensRange ≅
      (spectrumAmbientSheaf f J M V).over (spectrumOverlapToSpace f J U V).opensRange :=
  spectrumOverlapSheafImageIso f J M U V

/-- The original chart transition with named ambient module types. -/
@[irreducible]
def spectrumAmbientChartImageTransition (U V : X.affineOpens) :
    (spectrumAmbientSheaf f J M U).over
        (spectrumImageOpen f J U ⊓ spectrumImageOpen f J V) ≅
      (spectrumAmbientSheaf f J M V).over
        (spectrumImageOpen f J U ⊓ spectrumImageOpen f J V) :=
  spectrumChartImageTransition f J M U V

/-- The ambient chart transition reindexes the overlap image comparison. -/
lemma spectrumAmbientChartImageTransition_eq (U V : X.affineOpens) :
    spectrumAmbientChartImageTransition f J M U V =
      Eq.mpr (congrArg (fun A ↦ (spectrumAmbientSheaf f J M U).over A ≅
        (spectrumAmbientSheaf f J M V).over A)
        (spectrumOverlapToSpace_opensRange f J U V).symm)
        (spectrumAmbientOverlapImageIso f J M U V) := by
  unfold spectrumAmbientChartImageTransition spectrumAmbientOverlapImageIso
  exact spectrumChartTransition_eq_overlapCoefficientImageIso f J M U V

/-- The ambient image comparison extends the actual pullback comparison. -/
lemma spectrumAmbientOverlapImageIso_hom (U V : X.affineOpens) :
    (spectrumAmbientOverlapImageIso f J M U V).hom =
      localHom (M := spectrumAmbientSheaf f J M U) (N := spectrumAmbientSheaf f J M V)
        (spectrumOverlapToSpace f J U V) (spectrumOverlapAmbientSheafIso f J M U V).hom := by
  unfold spectrumAmbientOverlapImageIso
  exact spectrumOverlapSheafImageIso_hom f J M U V

end FLT.Mazur.BaseAdicRees
