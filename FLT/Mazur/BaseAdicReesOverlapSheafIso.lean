/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesOverlapNormalization
public import FLT.Mazur.BaseAdicReesSpectrumOverlapSheafIso

/-!
# Full-overlap isomorphisms of the original Rees model sheaves

The glued comparison is expressed with the original chart sheaves and
recovers the original local coefficient maps on every common affine chart.
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

/-- The full-overlap isomorphism of the two original relative model sheaves. -/
def modelOverlapSheafIso (U V : X.affineOpens) :
    (pullback (Limits.pullback.fst (chartSpaceMap f J U) (chartSpaceMap f J V))).obj
        (modelSheaf f J U M) ≅
      (pullback (Limits.pullback.snd (chartSpaceMap f J U) (chartSpaceMap f J V))).obj
        (modelSheaf f J V M) :=
  spectrumOverlapSheafIso f J M U V

/-- The full-overlap isomorphism recovers each original local coefficient comparison. -/
lemma modelOverlapSheafIso_pullback {U V W : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) :
    (pullback (modelOverlapChart f J i j)).map (modelOverlapSheafIso f J M U V).hom =
      modelOverlapSheafMap f J M i j := by
  calc
    _ = spectrumOverlapSheafMap f J M i j :=
      spectrumOverlapSheafIso_pullback f J M U V i j
    _ = _ := spectrumOverlapSheafMap_eq f J M i j

end FLT.Mazur.BaseAdicRees
