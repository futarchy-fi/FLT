/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesOverlapSheafMap
public import FLT.Mazur.BaseAdicReesSpectrumOverlapSheafMap

/-!
# Original normalization of the fixed-presentation overlap maps

Naming the spectra and geometric projections does not change the actual
coefficient morphisms supplied to full-overlap gluing.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped TensorProduct

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

attribute [local semireducible] modelSpectrum
attribute [local irreducible] Scheme.Modules.pullback modelAffineOverlap modelMap modelSheaf
attribute [local irreducible] modelOverlapChart SheafPullbackLocalComparison.transport

/-- Fixing spectrum presentations leaves the original overlap morphism unchanged. -/
lemma spectrumOverlapSheafMap_eq {U V W : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) :
    spectrumOverlapSheafMap f J M i j = modelOverlapSheafMap f J M i j := by
  unfold spectrumOverlapSheafMap modelOverlapSheafMap
  rfl

end FLT.Mazur.BaseAdicRees
