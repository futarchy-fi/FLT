/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSheafIso

/-!
# Coherent comparisons on common affine Rees charts

The actual model comparisons obey the cocycle on any common affine chart
and commute with further affine refinements.
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

attribute [local irreducible] modelRestriction modelCompositeIso Scheme.Modules.pullback

/-- The normalized comparison on an arbitrary common affine chart. -/
def modelAffineOverlap {U V W : X.affineOpens} (h : W.1 ≤ U.1) (k : W.1 ≤ V.1) :
    (pullback (modelMap f J h)).obj (modelSheaf f J U M) ≅
      (pullback (modelMap f J k)).obj (modelSheaf f J V M) :=
  modelPullbackIso f J M h ≪≫ (modelPullbackIso f J M k).symm

/-- Comparison retains both of the original relative restriction maps. -/
lemma modelAffineOverlap_hom_comp {U V W : X.affineOpens}
    (h : W.1 ≤ U.1) (k : W.1 ≤ V.1) :
    (modelAffineOverlap f J M h k).hom ≫ modelRestriction f J M k =
      modelRestriction f J M h := by
  change ((modelPullbackIso f J M h).hom ≫ (modelPullbackIso f J M k).inv) ≫
    (modelPullbackIso f J M k).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, modelPullbackIso_hom]

/-- Comparing a chart to itself on a refinement gives the identity. -/
lemma modelAffineOverlap_self {U W : X.affineOpens} (h : W.1 ≤ U.1) :
    (modelAffineOverlap f J M h h).hom = 𝟙 _ := by
  let _ := modelRestriction_isIso f J M h
  apply (cancel_mono (modelRestriction f J M h)).mp
  rw [modelAffineOverlap_hom_comp, Category.id_comp]

/-- Reversing the two ambient charts inverts their comparison. -/
lemma modelAffineOverlap_symm {U V W : X.affineOpens}
    (h : W.1 ≤ U.1) (k : W.1 ≤ V.1) :
    (modelAffineOverlap f J M h k).symm = modelAffineOverlap f J M k h := by
  apply Iso.ext
  rfl

/-- The model cocycle holds on every common affine refinement. -/
lemma modelAffineOverlap_cocycle {U V T W : X.affineOpens}
    (h : W.1 ≤ U.1) (k : W.1 ≤ V.1) (l : W.1 ≤ T.1) :
    (modelAffineOverlap f J M h k).hom ≫ (modelAffineOverlap f J M k l).hom =
      (modelAffineOverlap f J M h l).hom := by
  let _ := modelRestriction_isIso f J M l
  apply (cancel_mono (modelRestriction f J M l)).mp
  rw [Category.assoc, modelAffineOverlap_hom_comp,
    modelAffineOverlap_hom_comp, modelAffineOverlap_hom_comp]

/-- Affine comparisons commute with further affine refinements and pullback composition. -/
lemma modelAffineOverlap_refine {U V W Z : X.affineOpens}
    (h : W.1 ≤ U.1) (k : W.1 ≤ V.1) (l : Z.1 ≤ W.1) :
    (pullback (modelMap f J l)).map (modelAffineOverlap f J M h k).hom ≫
        (modelCompositeIso f J M l k).hom =
      (modelCompositeIso f J M l h).hom ≫
        (modelAffineOverlap f J M (l.trans h) (l.trans k)).hom := by
  let _ := modelRestriction_isIso f J M (l.trans k)
  apply (cancel_mono (modelRestriction f J M (l.trans k))).mp
  rw [Category.assoc, Category.assoc, modelAffineOverlap_hom_comp,
    ← modelRestriction_comp_forward, ← modelRestriction_comp_forward,
    ← Category.assoc, ← Functor.map_comp, modelAffineOverlap_hom_comp]

end FLT.Mazur.BaseAdicRees
