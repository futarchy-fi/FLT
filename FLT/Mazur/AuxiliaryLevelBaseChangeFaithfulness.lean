/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryLevelBaseChange
public import FLT.Mazur.AuxiliaryLevelFaithfulRepresentation
public import FLT.Mazur.OverPullbackSection

/-!
# Universal faithfulness across the actual base-change adjunction

Every test over the old base mapping to the parameter already has a map to the
new base. Thus the equation-scheme comparison preserves and reflects universal
faithfulness, including nilpotent and singular tests.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (g : T ⟶ S) (E : Over S) [GrpObj E]
  (A : Type) [Group A] [Fintype A]

/-- Transport an original marking parameter through the actual group adjunction. -/
def changeBasePoint {U : Over T} (p : (Over.map g).obj U ⟶ homScheme E A) :
    U ⟶ homScheme ((Over.pullback g).obj E) A :=
  liftMarking _ A (GroupMarkingBaseChange.marking g E U (markingOf E A p))

/-- Each transported value retains the original scheme morphism after projection. -/
@[reassoc] theorem changeBasePoint_value_fst {U : Over T}
    (p : (Over.map g).obj U ⟶ homScheme E A) (a : A) :
    (changeBasePoint g E A p ≫ value ((Over.pullback g).obj E) A a).left ≫
      pullback.fst E.hom g = (p ≫ value E A a).left := by
  rw [changeBasePoint, liftMarking_value, GroupMarkingBaseChange.marking_fst]
  rfl

/-- The point construction is the actual equation-scheme comparison. -/
theorem changeBasePoint_eq {U : Over T}
    (p : (Over.map g).obj U ⟶ homScheme E A) :
    changeBasePoint g E A p =
      (Over.mapPullbackAdj g).homEquiv U (homScheme E A) p ≫
        (homSchemeBaseChangeIso g E A).hom := by
  apply homScheme_ext
  intro a
  rw [changeBasePoint, liftMarking_value, Category.assoc]
  change _ = _ ≫ homSchemeBaseChangeHom g E A ≫ _
  rw [homSchemeBaseChangeHom_value, ← baseChangeMarkingEquiv_apply]
  change _ = GroupMarkingBaseChange.marking g E U
    (markingOf E A (((Over.mapPullbackAdj g).homEquiv U _).symm
      ((Over.mapPullbackAdj g).homEquiv U _ p))) a
  rw [Equiv.symm_apply_apply]

/-- Universal faithfulness is unchanged on all tests, not just on global sections. -/
theorem changeBasePoint_universallyFaithful_iff {U : Over T}
    (p : (Over.map g).obj U ⟶ homScheme E A) :
    UniversallyFaithful ((Over.pullback g).obj E) A (changeBasePoint g E A p) ↔
      UniversallyFaithful E A p := by
  constructor
  · intro hp V k hV a b hab
    let W : Over T := Over.mk (k.left ≫ U.hom)
    let l : W ⟶ U := Over.homMk k.left rfl
    apply hp W l hV
    change (l ≫ changeBasePoint g E A p) ≫ value _ A a =
      (l ≫ changeBasePoint g E A p) ≫ value _ A b
    apply OverPullbackSection.hom_ext
    rw [Category.assoc, Category.assoc]
    change (l.left ≫ (changeBasePoint g E A p ≫ value _ A a).left) ≫ _ =
      (l.left ≫ (changeBasePoint g E A p ≫ value _ A b).left) ≫ _
    rw [Category.assoc, Category.assoc, changeBasePoint_value_fst,
      changeBasePoint_value_fst]
    have he := congrArg Over.Hom.left hab
    change (k.left ≫ p.left) ≫ (value E A a).left =
      (k.left ≫ p.left) ≫ (value E A b).left at he
    simpa only [Over.comp_left, Category.assoc, l, Over.homMk_left] using he
  · intro hp V k hV a b hab
    apply hp ((Over.map g).obj V) ((Over.map g).map k) hV
    apply Over.OverMorphism.ext
    have he := congrArg (fun f ↦ f.left ≫ pullback.fst E.hom g) hab
    change ((k ≫ changeBasePoint g E A p) ≫ value _ A a).left ≫ _ =
      ((k ≫ changeBasePoint g E A p) ≫ value _ A b).left ≫ _ at he
    rw [Category.assoc, Category.assoc] at he
    change (k.left ≫ (changeBasePoint g E A p ≫ value _ A a).left) ≫ _ =
      (k.left ≫ (changeBasePoint g E A p ≫ value _ A b).left) ≫ _ at he
    rw [Category.assoc, Category.assoc, changeBasePoint_value_fst,
      changeBasePoint_value_fst] at he
    change (k.left ≫ p.left) ≫ (value E A a).left =
      (k.left ≫ p.left) ≫ (value E A b).left
    simpa only [Over.comp_left, Category.assoc] using he

end FLT.Mazur.AuxiliaryLevel
