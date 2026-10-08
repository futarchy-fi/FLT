/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesAffineOverlap

/-!
# Geometric normalization of affine coefficient refinement

The coefficient-composition wrapper equals the geometric chart comparison.
This explicit equality keeps concrete tensor definitions out of subsequent
refinement proofs.
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

attribute [local irreducible] Scheme.Modules.pullback
attribute [local irreducible] modelMap
attribute [local irreducible] chartSpaceMap modelSheaf
attribute [local irreducible] modelAffineOverlap
attribute [local irreducible] AffineIteratedPullbackSections.compositeIso

/-- The coefficient composition wrapper is the geometric chart comparison. -/
lemma modelCompositeIso_eq_chart {U V W : X.affineOpens}
    (i : U.1 ≤ V.1) (j : V.1 ≤ W.1) :
    modelCompositeIso f J M i j =
      AffineIteratedPullbackSections.compositeIso
        (modelMap f J i) (modelMap f J j)
        (modelMap f J (i.trans j)) (modelMap_comp f J i j)
        (modelSheaf f J W M) := rfl

/-- Affine refinement stated entirely with the geometric chart comparison. -/
lemma modelAffineOverlap_refine_chart {U V W Z : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) (k : Z.1 ≤ W.1) :
    (pullback (modelMap f J k)).map
          (modelAffineOverlap f J M i j).hom ≫
        (AffineIteratedPullbackSections.compositeIso
          (modelMap f J k) (modelMap f J j)
          (modelMap f J (k.trans j)) (modelMap_comp f J k j)
          (modelSheaf f J V M)).hom =
      (AffineIteratedPullbackSections.compositeIso
          (modelMap f J k) (modelMap f J i)
          (modelMap f J (k.trans i)) (modelMap_comp f J k i)
          (modelSheaf f J U M)).hom ≫
        (modelAffineOverlap f J M (k.trans i) (k.trans j)).hom := by
  rw [← modelCompositeIso_eq_chart, ← modelCompositeIso_eq_chart]
  exact modelAffineOverlap_refine f J M i j k

end FLT.Mazur.BaseAdicRees
