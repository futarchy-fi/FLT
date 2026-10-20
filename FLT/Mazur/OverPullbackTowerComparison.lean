/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OverPullbackCoherence
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# Group-compatible recovery across a specified base tower

The canonical comparison for a composite base map retains its original
projection and preserves monoid structures after equality of base maps.
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

/-- Direct recovery compares canonically with recovery through an intermediate base. -/
def towerIso : Over.pullback k ≅ Over.pullback g ⋙ Over.pullback h :=
  eqToIso (congrArg (fun f : U ⟶ S => Over.pullback f) w.symm) ≪≫ Over.pullbackComp h g

/-- The tower comparison retains the full original projection. -/
@[reassoc] theorem towerIso_fst_fst (X : Over S) :
    ((towerIso g h k w).hom.app X).left ≫
      pullback.fst (pullback.snd X.hom g) h ≫ pullback.fst X.hom g =
        pullback.fst X.hom k := by
  subst k
  simpa only [towerIso, eqToIso_refl, Iso.trans_hom, Iso.refl_hom,
    NatTrans.id_app, NatTrans.comp_app, Category.id_comp] using comp_left_fst_fst g h X

instance towerIso_isMonHom (X : Over S) [MonObj X] :
    IsMonHom ((towerIso g h k w).hom.app X) := by
  exact inferInstanceAs
    (IsMonHom ((Functor.mapMonNatTrans (towerIso g h k w).hom).app (Mon.mk X)).hom)

end FLT.Mazur.OverPullbackCoherence
