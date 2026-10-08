/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpectrumSheafDescent

/-!
# A global model for the original Rees sheaves

The descended sheaf is locally finitely presented and recovers each original
model on the actual relative chart cover, with no change of coefficient modules.
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

attribute [local semireducible] modelSpectrum
attribute [local irreducible] Scheme.Modules.pullback modelSheaf

/-- The global relative Rees model descended from the original affine modules. -/
def globalModelSheaf : (relativeSpace f J).Modules := spectrumDescendedSheaf f J M

/-- The original affine finite presentations give a global finite presentation. -/
instance globalModelSheaf_isFinitePresentation [IsNoetherianRing R] :
    (globalModelSheaf f J M).IsFinitePresentation :=
  spectrumDescendedSheaf_isFinitePresentation f J M

/-- Restriction to each original tensor chart recovers its original model sheaf. -/
def globalModelSheafChartIso (V : X.affineOpens) :
    (globalModelSheaf f J M).restrict (chartSpaceMap f J V) ≅ modelSheaf f J V M :=
  spectrumDescendedSheafChartIso f J M V

/-- The global model recovers the original sheaves on the original relative chart cover. -/
def globalModelSheafCoverIso (V : (chartCover f J).I₀) :
    (globalModelSheaf f J M).restrict ((chartCover f J).f V) ≅ modelSheaf f J V M :=
  globalModelSheafChartIso f J M V

end FLT.Mazur.BaseAdicRees
