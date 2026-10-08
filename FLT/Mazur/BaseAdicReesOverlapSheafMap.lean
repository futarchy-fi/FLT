/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesAffineOverlap
public import FLT.Mazur.BaseAdicReesOverlapCover
public import FLT.Mazur.SheafPullbackLocalComparison

/-!
# Actual sheaf comparisons on the full Rees overlap charts

The normalized affine isomorphisms give maps between the pullbacks of the
two fixed sheaves on the full overlap. Refinement invariance is a separate step.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X]
  (M : X.Modules) [M.IsFinitePresentation]

attribute [local irreducible] Scheme.Modules.pullback modelAffineOverlap modelCompositeIso
attribute [local irreducible] AffineIteratedPullbackSections.compositeIso

/-- The two model sheaves on the overlap are compared on a common affine chart. -/
def modelOverlapSheafMap {U V W : X.affineOpens} (h : W.1 ≤ U.1) (k : W.1 ≤ V.1) :
    (pullback (modelOverlapChart f J h k)).obj
        ((pullback (Limits.pullback.fst (chartSpaceMap f J U) (chartSpaceMap f J V))).obj
          (modelSheaf f J U M)) ⟶
      (pullback (modelOverlapChart f J h k)).obj
        ((pullback (Limits.pullback.snd (chartSpaceMap f J U) (chartSpaceMap f J V))).obj
          (modelSheaf f J V M)) :=
  SheafPullbackLocalComparison.transport (modelOverlapChart f J h k)
    (Limits.pullback.fst _ _) (Limits.pullback.snd _ _)
    (modelMap f J h) (modelMap f J k)
    (modelOverlapChart_fst f J h k) (modelOverlapChart_snd f J h k)
    (modelSheaf f J U M) (modelSheaf f J V M) (modelAffineOverlap f J M h k).hom

/-- The transported actual coefficient comparison is invertible. -/
instance modelOverlapSheafMap_isIso {U V W : X.affineOpens}
    (h : W.1 ≤ U.1) (k : W.1 ≤ V.1) : IsIso (modelOverlapSheafMap f J M h k) := by
  unfold modelOverlapSheafMap
  infer_instance

/-- Transport to the full overlap retains the normalized affine comparison. -/
lemma modelOverlapSheafMap_normalize {U V W : X.affineOpens}
    (h : W.1 ≤ U.1) (k : W.1 ≤ V.1) :
    modelOverlapSheafMap f J M h k ≫
        (SheafPullbackPathComparison.comparison (modelOverlapChart f J h k)
          (Limits.pullback.snd _ _) (modelMap f J k)
          (modelOverlapChart_snd f J h k)).hom.app (modelSheaf f J V M) =
      (SheafPullbackPathComparison.comparison (modelOverlapChart f J h k)
          (Limits.pullback.fst _ _) (modelMap f J h)
          (modelOverlapChart_fst f J h k)).hom.app (modelSheaf f J U M) ≫
        (modelAffineOverlap f J M h k).hom :=
  SheafPullbackLocalComparison.transport_normalize _ _ _ _ _ _ _ _ _ _

end FLT.Mazur.BaseAdicRees
