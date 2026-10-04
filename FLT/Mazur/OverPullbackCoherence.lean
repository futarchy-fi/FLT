/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Projection formulas for canonical pullback comparisons

The comparisons defined by adjunctions have the expected projection maps.
These formulas allow coherence to be checked by the pullback universal property.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.OverPullbackCoherence
universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {S T U : C}

/-- The identity comparison is the first pullback projection. -/
@[simp]
theorem id_left (X : Over S) :
    (Over.pullbackId.hom.app X).left = pullback.fst X.hom (𝟙 S) := by
  simp [Over.pullbackId, conjugateIsoEquiv, conjugateEquiv_apply_app,
    Over.mapPullbackAdj_counit_app, Over.mapId]

/-- The composition comparison preserves the projection to the original object. -/
@[reassoc (attr := simp)]
theorem comp_left_fst_fst (g : T ⟶ S) (h : U ⟶ T) (X : Over S) :
    ((Over.pullbackComp h g).hom.app X).left ≫
      pullback.fst (pullback.snd X.hom g) h ≫ pullback.fst X.hom g =
        pullback.fst X.hom (h ≫ g) := by
  simp [Over.pullbackComp, conjugateIsoEquiv, conjugateEquiv_apply_app,
    Over.mapPullbackAdj_counit_app, Over.mapPullbackAdj_unit_app, Over.mapComp,
    Category.assoc]

end FLT.Mazur.OverPullbackCoherence
