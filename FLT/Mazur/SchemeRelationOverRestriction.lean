/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationDoubleRestriction
public import FLT.Mazur.RelativeRelationArrowCalculus

/-!
# Forgetting the base of a full relation restriction

The two endpoint pullbacks in `Over S` give exactly the scheme-level double
restriction. The comparison retains the original arrow and both endpoints.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationRestriction
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {A X Y : Over S} (p q : A ⟶ X) (k : Y ⟶ X)

/-- The first endpoint pullback remains a pullback after forgetting the base. -/
theorem overFirstSquare :
    IsPullback (pullback.fst p k).left (pullback.snd p k).left p.left k.left :=
  (IsPullback.of_hasPullback p k).map (Over.forget S)

/-- The second independent endpoint pullback also remains a pullback. -/
theorem overSecondSquare :
    IsPullback (pullback.fst (pullback.fst p k ≫ q) k).left
      (pullback.snd (pullback.fst p k ≫ q) k).left
      (pullback.fst p k ≫ q).left k.left :=
  (IsPullback.of_hasPullback (pullback.fst p k ≫ q) k).map (Over.forget S)

/-- The original arrow of the double pullback in the slice category. -/
def overArrow : (pullback (pullback.fst p k ≫ q) k).left ⟶ A.left :=
  (pullback.fst (pullback.fst p k ≫ q) k).left ≫ (pullback.fst p k).left

/-- Its first endpoint, with the original base forgotten. -/
def overFst : (pullback (pullback.fst p k ≫ q) k).left ⟶ Y.left :=
  (pullback.fst (pullback.fst p k ≫ q) k).left ≫ (pullback.snd p k).left

/-- Its second endpoint, independent of the first one. -/
def overSnd : (pullback (pullback.fst p k ≫ q) k).left ⟶ Y.left :=
  (pullback.snd (pullback.fst p k ≫ q) k).left

/-- The canonical map from the forgotten double pullback to the scheme restriction. -/
def overToDouble : (pullback (pullback.fst p k ≫ q) k).left ⟶
    doubleDomain p.left q.left k.left :=
  lift p.left q.left k.left (overArrow p q k) (overFst p q k) (overSnd p q k)
    (by
      dsimp only [overArrow, overFst]
      rw [Category.assoc, ← Over.comp_left, pullback.condition, Over.comp_left,
        ← Category.assoc])
    (by
      dsimp only [overArrow, overSnd]
      rw [Category.assoc, ← Over.comp_left, ← Over.comp_left, pullback.condition]
      rfl)

/-- Recover the first pullback from the original arrow and first scheme endpoint. -/
def doubleToOverFirst : doubleDomain p.left q.left k.left ⟶ (pullback p k).left :=
  (overFirstSquare p k).lift (arrow p.left q.left k.left) (fst p.left q.left k.left)
    (arrow_fst p.left q.left k.left)

@[reassoc]
theorem doubleToOverFirst_arrow : doubleToOverFirst p q k ≫ (pullback.fst p k).left =
    arrow p.left q.left k.left := (overFirstSquare p k).lift_fst _ _ _

@[reassoc]
theorem doubleToOverFirst_fst : doubleToOverFirst p q k ≫ (pullback.snd p k).left =
    fst p.left q.left k.left := (overFirstSquare p k).lift_snd _ _ _

/-- Recover the full slice pullback using both independent scheme endpoints. -/
def doubleToOver : doubleDomain p.left q.left k.left ⟶
    (pullback (pullback.fst p k ≫ q) k).left :=
  (overSecondSquare p q k).lift (doubleToOverFirst p q k) (snd p.left q.left k.left)
    (by rw [Over.comp_left, doubleToOverFirst_arrow_assoc, arrow_snd])

@[reassoc]
theorem doubleToOver_arrow : doubleToOver p q k ≫ overArrow p q k =
    arrow p.left q.left k.left := by
  dsimp only [doubleToOver, overArrow]
  rw [← Category.assoc, (overSecondSquare p q k).lift_fst, doubleToOverFirst_arrow]

@[reassoc]
theorem doubleToOver_fst : doubleToOver p q k ≫ overFst p q k =
    fst p.left q.left k.left := by
  dsimp only [doubleToOver, overFst]
  rw [← Category.assoc, (overSecondSquare p q k).lift_fst, doubleToOverFirst_fst]

@[reassoc]
theorem doubleToOver_snd : doubleToOver p q k ≫ overSnd p q k =
    snd p.left q.left k.left := (overSecondSquare p q k).lift_snd _ _ _

@[reassoc]
theorem overToDouble_arrow : overToDouble p q k ≫ arrow p.left q.left k.left =
    overArrow p q k := lift_arrow _ _ _ _ _ _ _ _

@[reassoc]
theorem overToDouble_fst : overToDouble p q k ≫ fst p.left q.left k.left =
    overFst p q k := lift_fst _ _ _ _ _ _ _ _

@[reassoc]
theorem overToDouble_snd : overToDouble p q k ≫ snd p.left q.left k.left =
    overSnd p q k := lift_snd _ _ _ _ _ _ _ _

/-- Maps to a full scheme restriction are determined by the arrow and both endpoints. -/
theorem double_hom_ext {T : Scheme.{u}} {a b : T ⟶ doubleDomain p.left q.left k.left}
    (ha : a ≫ arrow p.left q.left k.left = b ≫ arrow p.left q.left k.left)
    (hx : a ≫ fst p.left q.left k.left = b ≫ fst p.left q.left k.left)
    (hy : a ≫ snd p.left q.left k.left = b ≫ snd p.left q.left k.left) : a = b := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · exact ha
    · exact hx
  · exact hy

/-- Forgetting the base identifies the actual full restrictions, including every arrow. -/
def overDoubleIso : (pullback (pullback.fst p k ≫ q) k).left ≅
    doubleDomain p.left q.left k.left where
  hom := overToDouble p q k
  inv := doubleToOver p q k
  hom_inv_id := by
    apply (overSecondSquare p q k).hom_ext
    · apply (overFirstSquare p k).hom_ext
      · change _ ≫ overArrow p q k = _
        rw [Category.assoc, doubleToOver_arrow, overToDouble_arrow]
        rfl
      · change _ ≫ overFst p q k = _
        rw [Category.assoc, doubleToOver_fst, overToDouble_fst]
        rfl
    · change _ ≫ overSnd p q k = _
      rw [Category.assoc, doubleToOver_snd, overToDouble_snd]
      rfl
  inv_hom_id := by
    apply double_hom_ext p q k
    · rw [Category.assoc, overToDouble_arrow, doubleToOver_arrow, Category.id_comp]
    · rw [Category.assoc, overToDouble_fst, doubleToOver_fst, Category.id_comp]
    · rw [Category.assoc, overToDouble_snd, doubleToOver_snd, Category.id_comp]

end FLT.Mazur.SchemeRelationRestriction
