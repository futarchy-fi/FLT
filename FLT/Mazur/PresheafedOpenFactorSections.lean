/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Geometry.RingedSpace.PresheafedSpace

/-!
# Sections of a morphism factoring through an open subspace

The top-section pullback of an open factor is the ambient pullback on that
open, with the source and target section transports written explicitly.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.PresheafedOpenFactorSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type u} [Category.{v} C] {X Y : PresheafedSpace C}

/-- Pullback along an open factor computes the original ambient section map. -/
theorem factor_top (W : Opens Y)
    (f : X ⟶ Y.restrict W.isOpenEmbedding)
    (h : ⊤ ≤ (Opens.map (f ≫ Y.ofRestrict W.isOpenEmbedding).base).obj W) :
    Y.presheaf.map (eqToHom (congrArg op
      (Opens.isOpenEmbedding_obj_top W).symm)) ≫ PresheafedSpace.Γ.map f.op =
      (f ≫ Y.ofRestrict W.isOpenEmbedding).c.app (op W) ≫
        X.presheaf.map (homOfLE h).op := by
  let i := Y.ofRestrict W.isOpenEmbedding
  have hi : ⊤ ≤ (Opens.map i.base).obj W := by
    intro x _
    exact x.property
  have hn := f.c.naturality (homOfLE hi).op
  have ht : i.c.app (op W) ≫
      (Y.restrict W.isOpenEmbedding).presheaf.map (homOfLE hi).op =
      Y.presheaf.map (eqToHom (congrArg op
        (Opens.isOpenEmbedding_obj_top W).symm)) := by
    dsimp only [i, PresheafedSpace.ofRestrict_c_app,
      PresheafedSpace.restrict_presheaf, Functor.comp_map, Functor.op_map]
    rw [← Functor.map_comp]
    congr 1
  rw [PresheafedSpace.Γ_map_op, ← ht, Category.assoc]
  erw [hn]
  rw [← Category.assoc]
  congr 1

/-- The same formula with the ambient composite identified explicitly. -/
theorem factor_top_of_comp (W : Opens Y)
    (f : X ⟶ Y.restrict W.isOpenEmbedding) (g : X ⟶ Y)
    (hf : f ≫ Y.ofRestrict W.isOpenEmbedding = g)
    (h : ⊤ ≤ (Opens.map g.base).obj W) :
    Y.presheaf.map (eqToHom (congrArg op
      (Opens.isOpenEmbedding_obj_top W).symm)) ≫ PresheafedSpace.Γ.map f.op =
      g.c.app (op W) ≫ X.presheaf.map (homOfLE h).op := by
  subst g
  exact factor_top W f h

end FLT.Mazur.PresheafedOpenFactorSections
