/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupMarkingBaseChange
public import FLT.Mazur.GroupMarkingTransport
public import Mathlib.Algebra.Group.Prod

/-!
# Full markings on an actual cartesian realization of a group

Combine the group-valued pullback adjunction with a specified group isomorphism.
The resulting full marking retains each original scheme map after projection
and preserves and reflects injectivity, including on nonreduced tests.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GroupMarkingCartesianTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S T : Scheme} (g : T ⟶ S) (G : CommGrp (Over S)) (H : CommGrp (Over T))
  (e : (Over.pullback g).mapCommGrp.obj G ≅ H) (U : Over T)
  {A : Type*} [Monoid A]

/-- Transport every original label through the actual cartesian group comparison. -/
def marking (m : A →* ((Over.map g).obj U ⟶ G.X)) : A →* (U ⟶ H.X) :=
  GroupMarkingTransport.transport ((Over.pullback g).mapCommGrp.obj G) H e
    (GroupMarkingBaseChange.marking g G.X U m)

/-- The full marking retains each original scheme morphism after the actual projection. -/
@[reassoc] theorem marking_projection (m : A →* ((Over.map g).obj U ⟶ G.X)) (a : A) :
    (marking g G H e U m a).left ≫ e.inv.hom.hom.hom.left ≫
      pullback.fst G.X.hom g = (m a).left := by
  have he : e.hom.hom.hom.hom ≫ e.inv.hom.hom.hom = 𝟙 _ :=
    congrArg (fun f ↦ f.hom.hom.hom) e.hom_inv_id
  change (GroupMarkingBaseChange.marking g G.X U m a ≫ e.hom.hom.hom.hom).left ≫ _ = _
  rw [Over.comp_left, Category.assoc, ← Category.assoc e.hom.hom.hom.hom.left,
    ← Over.comp_left, he, Over.id_left, Category.id_comp]
  exact GroupMarkingBaseChange.marking_fst g G.X U m a

/-- Faithfulness is both preserved and reflected through the actual cartesian realization. -/
theorem marking_injective_iff (m : A →* ((Over.map g).obj U ⟶ G.X)) :
    Function.Injective (marking g G H e U m) ↔ Function.Injective m := by
  unfold marking
  rw [GroupMarkingTransport.transport_injective_iff]
  exact GroupMarkingBaseChange.marking_injective_iff g G.X U m

/-- Transport respects the two constituent factors of a mixed marking. -/
theorem marking_coprod {B : Type*} [Monoid B]
    (m : A →* ((Over.map g).obj U ⟶ G.X))
    (v : B →* ((Over.map g).obj U ⟶ G.X)) (a : A) (b : B) :
    marking g G H e U (m.coprod v) (a, b) =
      marking g G H e U m a * marking g G H e U v b := by
  have hm := (GroupMarkingBaseChange.pointsMulEquiv g G.X U).map_mul (m a) (v b)
  have he := congrArg
    (fun z : U ⟶ ((Over.pullback g).mapCommGrp.obj G).X ↦ z ≫ e.hom.hom.hom.hom) hm
  change marking g G H e U (m.coprod v) (a, b) =
    ((GroupMarkingBaseChange.pointsMulEquiv g G.X U (m a) :
      U ⟶ ((Over.pullback g).mapCommGrp.obj G).X) *
      GroupMarkingBaseChange.pointsMulEquiv g G.X U (v b)) ≫ e.hom.hom.hom.hom at he
  rw [MonObj.mul_comp] at he
  exact he

/-- Projection to the original group detects equality of sections on the same extended test. -/
theorem point_ext (p q : U ⟶ H.X)
    (he : p.left ≫ e.inv.hom.hom.hom.left ≫ pullback.fst G.X.hom g =
      q.left ≫ e.inv.hom.hom.hom.left ≫ pullback.fst G.X.hom g) : p = q := by
  have hp : p ≫ e.inv.hom.hom.hom = q ≫ e.inv.hom.hom.hom := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa only [Over.comp_left, Category.assoc] using he
    · exact (p ≫ e.inv.hom.hom.hom).w.trans (q ≫ e.inv.hom.hom.hom).w.symm
  have hi : e.inv.hom.hom.hom ≫ e.hom.hom.hom.hom = 𝟙 _ :=
    congrArg (fun f ↦ f.hom.hom.hom) e.inv_hom_id
  have hc := congrArg (fun f ↦ f ≫ e.hom.hom.hom.hom) hp
  simpa only [Category.assoc, hi, Category.comp_id] using hc

/-- The actual cartesian marking commutes with every change of test scheme. -/
theorem marking_natural (m : A →* ((Over.map g).obj U ⟶ G.X))
    {V : Over T} (k : V ⟶ U) (a : A) :
    marking g G H e V
      (((yonedaGrpObj G.X).map ((Over.map g).map k).op).hom.comp m) a =
        k ≫ marking g G H e U m a := by
  apply point_ext g G H e V
  rw [marking_projection, Over.comp_left, Category.assoc, marking_projection]
  rfl

end FLT.Mazur.GroupMarkingCartesianTransport
