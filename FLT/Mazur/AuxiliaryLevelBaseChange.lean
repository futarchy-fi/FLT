/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryLevelHomScheme
public import FLT.Mazur.GroupMarkingBaseChange

/-!
# Finite marking schemes commute with arbitrary base change

The pullback adjunction identifies the represented group markings on every
test scheme. This constructs an isomorphism of the actual equation schemes,
without smoothness or reducedness assumptions on the group or either base.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (g : T ⟶ S) (E : Over S) [GrpObj E]
  (A : Type) [Group A] [Fintype A]

/-- The actual pulled-back marking scheme represents markings of the pulled-back group. -/
def baseChangeMarkingEquiv (U : Over T) :
    (U ⟶ (Over.pullback g).obj (homScheme E A)) ≃
      (A →* (U ⟶ (Over.pullback g).obj E)) :=
  ((Over.mapPullbackAdj g).homEquiv U (homScheme E A)).symm.trans
    ((markingEquiv E A ((Over.map g).obj U)).trans
      (GroupMarkingBaseChange.pointsMulEquiv g E U).monoidHomCongrRightEquiv)

/-- Every represented value is the actual pullback of the original universal value. -/
theorem baseChangeMarkingEquiv_apply {U : Over T}
    (f : U ⟶ (Over.pullback g).obj (homScheme E A)) (a : A) :
    baseChangeMarkingEquiv g E A U f a = f ≫ (Over.pullback g).map (value E A a) := by
  change (Over.mapPullbackAdj g).homEquiv U E
    (((Over.mapPullbackAdj g).homEquiv U (homScheme E A)).symm f ≫ value E A a) = _
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]

/-- The represented marking commutes with every test morphism. -/
theorem baseChangeMarkingEquiv_comp {U V : Over T} (k : U ⟶ V)
    (f : V ⟶ (Over.pullback g).obj (homScheme E A)) (a : A) :
    baseChangeMarkingEquiv g E A U (k ≫ f) a =
      k ≫ baseChangeMarkingEquiv g E A V f a := by
  rw [baseChangeMarkingEquiv_apply, baseChangeMarkingEquiv_apply, Category.assoc]

/-- Comparison from the actual pullback to the equation scheme over the new base. -/
def homSchemeBaseChangeHom :
    (Over.pullback g).obj (homScheme E A) ⟶ homScheme ((Over.pullback g).obj E) A :=
  liftMarking _ A (baseChangeMarkingEquiv g E A _ (𝟙 _))

/-- The comparison retains each original universal marked section. -/
@[reassoc] theorem homSchemeBaseChangeHom_value (a : A) :
    homSchemeBaseChangeHom g E A ≫ value ((Over.pullback g).obj E) A a =
      (Over.pullback g).map (value E A a) := by
  rw [homSchemeBaseChangeHom, liftMarking_value, baseChangeMarkingEquiv_apply,
    Category.id_comp]

/-- The inverse comparison supplied by the original represented marking. -/
def homSchemeBaseChangeInv :
    homScheme ((Over.pullback g).obj E) A ⟶ (Over.pullback g).obj (homScheme E A) :=
  (baseChangeMarkingEquiv g E A _).symm (universalMarking _ A)

/-- Projection of the inverse recovers the new base's original universal marking. -/
@[reassoc] theorem homSchemeBaseChangeInv_value (a : A) :
    homSchemeBaseChangeInv g E A ≫ (Over.pullback g).map (value E A a) =
      value ((Over.pullback g).obj E) A a := by
  rw [← baseChangeMarkingEquiv_apply, homSchemeBaseChangeInv, Equiv.apply_symm_apply]
  rfl

/-- The actual finite marking scheme commutes with every change of base. -/
def homSchemeBaseChangeIso :
    (Over.pullback g).obj (homScheme E A) ≅ homScheme ((Over.pullback g).obj E) A where
  hom := homSchemeBaseChangeHom g E A
  inv := homSchemeBaseChangeInv g E A
  hom_inv_id := by
    apply (baseChangeMarkingEquiv g E A _).injective
    apply MonoidHom.ext
    intro a
    rw [baseChangeMarkingEquiv_apply, baseChangeMarkingEquiv_apply,
      Category.assoc, homSchemeBaseChangeInv_value, homSchemeBaseChangeHom_value,
      Category.id_comp]
  inv_hom_id := by
    apply homScheme_ext
    intro a
    rw [Category.assoc, homSchemeBaseChangeHom_value, homSchemeBaseChangeInv_value,
      Category.id_comp]

end FLT.Mazur.AuxiliaryLevel
