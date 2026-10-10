/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpectrumImageSheaf
public import FLT.Mazur.BaseAdicReesSpectrumOverlapSheafIso
public import FLT.Mazur.ModuleSheafOverlapImageTransition

/-!
# Coefficient transitions on image-open intersections

Transport the actual full-overlap coefficient comparisons to the slice
isomorphisms required by module-sheaf object gluing.
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
  (U V : X.affineOpens)

attribute [local semireducible] modelSpectrum
attribute [local instance] spectrumSpaceMap_isOpenImmersion
attribute [local irreducible] Scheme.Modules.pullback spectrumSheaf
attribute [local irreducible] spectrumOverlapSheafIso

/-- The original chart pushforwards are isomorphic on their image intersection. -/
def spectrumChartImageTransition :
    ((pushforward (spectrumSpaceMap f J U)).obj
        (spectrumSheaf f J M U)).over
          (spectrumImageOpen f J U ⊓ spectrumImageOpen f J V) ≅
      ((pushforward (spectrumSpaceMap f J V)).obj
        (spectrumSheaf f J M V)).over
          (spectrumImageOpen f J U ⊓ spectrumImageOpen f J V) := by
  have hr : (spectrumOverlapToSpace f J U V).opensRange =
      spectrumImageOpen f J U ⊓ spectrumImageOpen f J V :=
    TopologicalSpace.Opens.ext (spectrumOverlapToSpace_range f J U V)
  rw [← hr]
  exact ModuleSheafOverlapImageTransition.imageIso
    (spectrumSpaceMap f J U) (spectrumSpaceMap f J V)
    (spectrumOverlapFirst f J U V) (spectrumOverlapSecond f J U V)
    (spectrumOverlapToSpace f J U V) rfl Limits.pullback.condition.symm
    (spectrumOverlapSheafIso f J M U V)

/-- The actual image-open coefficient objects have linear transition isomorphisms. -/
def spectrumImageSheafTransition :
    ((pushforward (spectrumImageOpen f J U).ι).obj
        (spectrumImageSheaf f J M U)).over
          (spectrumImageOpen f J U ⊓ spectrumImageOpen f J V) ≅
      ((pushforward (spectrumImageOpen f J V).ι).obj
        (spectrumImageSheaf f J M V)).over
          (spectrumImageOpen f J U ⊓ spectrumImageOpen f J V) :=
  (SheafOfModules.overFunctor (relativeSpace f J).ringCatSheaf
      (spectrumImageOpen f J U ⊓ spectrumImageOpen f J V)).mapIso
        (spectrumImageSheafPushforwardIso f J M U) ≪≫
    spectrumChartImageTransition f J M U V ≪≫
    ((SheafOfModules.overFunctor (relativeSpace f J).ringCatSheaf
      (spectrumImageOpen f J U ⊓ spectrumImageOpen f J V)).mapIso
        (spectrumImageSheafPushforwardIso f J M V)).symm

end FLT.Mazur.BaseAdicRees
