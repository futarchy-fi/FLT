/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpectrumTripleAmbientMaps
public import FLT.Mazur.BaseAdicReesSpectrumTripleSheafCocycle
public import FLT.Mazur.ModuleSheafLocalHomNormalization
public import FLT.Mazur.ModuleSheafLocalIsoTransport

/-!
# The ambient triple coefficient cocycle

Coordinate recovery transfers the full coefficient cocycle to ambient
pushforwards and then to sections on every subopen of the triple image.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.BaseAdicRees

open ModuleSheafOpenImmersionLocalHom ModuleSheafMorphismGluing

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]
  (U V T : X.affineOpens)

attribute [local irreducible] Scheme.Modules.pullback spectrumSheaf
attribute [local irreducible] spectrumTripleFirstAmbientMap spectrumTripleLastAmbientMap
attribute [local irreducible] spectrumTripleOuterAmbientMap spectrumAmbientSheaf
attribute [local irreducible] spectrumTripleFirstAmbientCoordinate
attribute [local irreducible] spectrumTripleSecondAmbientCoordinate
attribute [local irreducible] spectrumTripleThirdAmbientCoordinate

/-- The normalized ambient coefficient comparisons satisfy the triple cocycle. -/
theorem spectrumTripleAmbientMap_cocycle :
    spectrumTripleFirstAmbientMap f J M U V T ≫ spectrumTripleLastAmbientMap f J M U V T =
      spectrumTripleOuterAmbientMap f J M U V T := by
  apply (cancel_mono (spectrumTripleThirdAmbientCoordinate f J M U V T).hom).mp
  rw [Category.assoc, spectrumTripleLastAmbientMap_coordinate,
    ← Category.assoc, spectrumTripleFirstAmbientMap_coordinate, Category.assoc,
    spectrumTripleSheafMap_cocycle, spectrumTripleOuterAmbientMap_coordinate]

/-- The ambient cocycle holds on every subopen of the actual triple image. -/
theorem spectrumTripleAmbientMap_cocycle_app
    (W : (relativeSpace f J).Opens) (hW : W ≤ (spectrumTripleToScheme f J U V T).opensRange)
    (s : Γ(spectrumAmbientSheaf f J M U, W)) :
    localApp (localHom (spectrumTripleToScheme f J U V T)
      (spectrumTripleLastAmbientMap f J M U V T)) hW
      (localApp (localHom (spectrumTripleToScheme f J U V T)
        (spectrumTripleFirstAmbientMap f J M U V T)) hW s) =
      localApp (localHom (spectrumTripleToScheme f J U V T)
        (spectrumTripleOuterAmbientMap f J M U V T)) hW s := by
  have h := congrArg (localHom (spectrumTripleToScheme f J U V T))
    (spectrumTripleAmbientMap_cocycle f J M U V T)
  rw [localHom_comp] at h
  have hs := congrArg (fun a ↦ localApp a hW s) h
  rw [localApp_comp_apply] at hs
  exact hs

end FLT.Mazur.BaseAdicRees
