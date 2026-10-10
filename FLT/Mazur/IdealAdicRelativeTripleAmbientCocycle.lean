/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeTripleAmbientMaps
public import FLT.Mazur.IdealAdicRelativeTripleCoefficientCocycle
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

namespace FLT.Mazur.IdealAdicGradedPullback

open ModuleSheafOpenImmersionLocalHom ModuleSheafMorphismGluing

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y) (U V T : X.affineOpens)

attribute [local irreducible] Scheme.Modules.pullback relativeChartCoefficientSheaf
attribute [local irreducible] relativeTripleFirstAmbientMap relativeTripleLastAmbientMap
attribute [local irreducible] relativeTripleOuterAmbientMap relativeAmbientCoefficient
attribute [local irreducible] relativeTripleFirstAmbientCoordinate
attribute [local irreducible] relativeTripleSecondAmbientCoordinate
attribute [local irreducible] relativeTripleThirdAmbientCoordinate

/-- The normalized ambient coefficient comparisons satisfy the triple cocycle. -/
theorem relativeTripleAmbientMap_cocycle :
    relativeTripleFirstAmbientMap J f U V T ≫ relativeTripleLastAmbientMap J f U V T =
      relativeTripleOuterAmbientMap J f U V T := by
  apply (cancel_mono (relativeTripleThirdAmbientCoordinate J f U V T).hom).mp
  rw [Category.assoc, relativeTripleLastAmbientMap_coordinate,
    ← Category.assoc, relativeTripleFirstAmbientMap_coordinate, Category.assoc,
    relativeTripleCoefficientMap_cocycle, relativeTripleOuterAmbientMap_coordinate]

/-- The ambient cocycle holds on every subopen of the actual triple image. -/
theorem relativeTripleAmbientMap_cocycle_app
    (W : (relativeScheme J f).Opens) (hW : W ≤ (relativeTripleToScheme J f U V T).opensRange)
    (s : Γ(relativeAmbientCoefficient J f U, W)) :
    localApp (localHom (relativeTripleToScheme J f U V T)
      (relativeTripleLastAmbientMap J f U V T)) hW
      (localApp (localHom (relativeTripleToScheme J f U V T)
        (relativeTripleFirstAmbientMap J f U V T)) hW s) =
      localApp (localHom (relativeTripleToScheme J f U V T)
        (relativeTripleOuterAmbientMap J f U V T)) hW s := by
  have h := congrArg (localHom (relativeTripleToScheme J f U V T))
    (relativeTripleAmbientMap_cocycle J f U V T)
  rw [localHom_comp] at h
  have hs := congrArg (fun a ↦ localApp a hW s) h
  rw [localApp_comp_apply] at hs
  exact hs

end FLT.Mazur.IdealAdicGradedPullback
