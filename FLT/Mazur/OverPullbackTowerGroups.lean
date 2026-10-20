/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OverPullbackTowerComparison

/-!
# Iterated group structures in the pullback tower

The composition comparison preserves the iterated group law. The monoidal
composition constraint accounts for the distinction between the composite
functor's transported monoid and two successive transported monoids.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace FLT.Mazur.OverPullbackCoherence

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Over.cartesianMonoidalCategory

universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {S T U : C} (g : T ⟶ S) (h : U ⟶ T) (k : U ⟶ S) (w : h ≫ g = k)

/-- The tower comparison preserves the actual twice-pulled-back monoid structure. -/
theorem towerIso_nested_isMonHom (X : Over S) [MonObj X] :
    @IsMonHom (Over U) _ _ ((Over.pullback k).obj X)
      ((Over.pullback h).obj ((Over.pullback g).obj X))
      (Functor.monObjObj (F := Over.pullback k) X)
      (Functor.monObjObj (F := Over.pullback h) ((Over.pullback g).obj X))
      ((towerIso g h k w).hom.app X) := by
  let a := (Functor.mapMonNatTrans (towerIso g h k w).hom).app (Mon.mk X)
  let b := (Functor.mapMonCompIso (F := Over.pullback g) (G := Over.pullback h)).hom.app
    (Mon.mk X)
  have hb : IsMonHom (a.hom ≫ b.hom) := inferInstance
  have hb_hom : b.hom = 𝟙 _ := rfl
  rw [hb_hom, Category.comp_id] at hb
  exact hb

end FLT.Mazur.OverPullbackCoherence
