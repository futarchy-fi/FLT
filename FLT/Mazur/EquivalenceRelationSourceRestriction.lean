/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedFrameRelation

/-!
# Restricting both independent original frame endpoints

Two arbitrary source maps define a two-endpoint pullback of the entire original
relation. Its universal property retains every original arrow, both independent
source lifts and all original coefficient morphisms. No relation branch is chosen.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.SourceRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  {I : Type} [Fintype I] {o : I} {U V : Scheme.{0}}
  (j : U ⟶ source p q I o) (k : V ⟶ source p q I o)

/-- The entire relation after restricting its first source endpoint. -/
def left : Scheme := pullback (relationFirst p q I o) j

/-- The entire relation after restricting both source endpoints independently. -/
def relation : Scheme :=
  pullback (pullback.fst (relationFirst p q I o) j ≫ relationSecond p q I o) k

/-- The unchanged original normalized relation morphism. -/
def original : relation j k ⟶ fullRelation p q I o :=
  pullback.fst _ _ ≫ pullback.fst (relationFirst p q I o) j

/-- The first endpoint in the restricted source. -/
def fst : relation j k ⟶ U := pullback.fst _ _ ≫ pullback.snd (relationFirst p q I o) j

/-- The independent second endpoint in its own restricted source. -/
def snd : relation j k ⟶ V := pullback.snd _ _

/-- The original first endpoint is retained exactly. -/
@[reassoc] theorem original_first :
    original j k ≫ relationFirst p q I o = fst j k ≫ j := by
  simp only [original, fst, Category.assoc, pullback.condition]

/-- The original second endpoint is retained exactly. -/
@[reassoc] theorem original_second :
    original j k ≫ relationSecond p q I o = snd j k ≫ k := by
  exact (Category.assoc _ _ _).trans pullback.condition

/-- The original relation coordinate, including its coefficient morphisms. -/
def arrow : relation j k ⟶ D := original j k ≫ relationArrow p q I o

/-- Restriction retains the original arrow's source equation. -/
@[reassoc] theorem arrow_first : arrow j k ≫ p = fst j k ≫ j ≫ first p q I o := by
  rw [arrow, Category.assoc, relationArrow_first, ← Category.assoc, original_first,
    Category.assoc]

/-- Restriction retains the original arrow's target equation. -/
@[reassoc] theorem arrow_second : arrow j k ≫ q = snd j k ≫ k ≫ first p q I o := by
  rw [arrow, Category.assoc, relationArrow_second, ← Category.assoc, original_second,
    Category.assoc]

/-- Every equalized coefficient map stays equal on the two independent source lifts. -/
@[reassoc] theorem coefficients {S : Scheme.{0}} (c : A ⟶ S) (hc : p ≫ c = q ≫ c) :
    fst j k ≫ j ≫ first p q I o ≫ c = snd j k ≫ k ≫ first p q I o ≫ c := by
  rw [← Category.assoc (j) _ _, ← Category.assoc, ← arrow_first,
    Category.assoc, hc, ← Category.assoc, arrow_second, Category.assoc, Category.assoc]

variable {T : Scheme.{0}} (u : T ⟶ U) (v : T ⟶ V) (a : T ⟶ D)
  (ha : a ≫ p = u ≫ j ≫ first p q I o)
  (hb : a ≫ q = v ≫ k ≫ first p q I o)

/-- Every original arrow with both source lifts factors through the entire restriction. -/
def lift : T ⟶ relation j k :=
  pullback.lift
    (pullback.lift (relationLift p q I o (u ≫ j) (v ≫ k) a
      (ha.trans (Category.assoc _ _ _).symm) (hb.trans (Category.assoc _ _ _).symm)) u
      (relationLift_first p q I o _ _ _ _ _)) v (by
        rw [pullback.lift_fst_assoc, relationLift_second])

/-- The universal lift keeps the first restricted endpoint. -/
@[reassoc] theorem lift_fst : lift j k u v a ha hb ≫ fst j k = u := by
  simp only [lift, fst, pullback.lift_fst_assoc, pullback.lift_snd]

/-- The universal lift keeps the independent second restricted endpoint. -/
@[reassoc] theorem lift_snd : lift j k u v a ha hb ≫ snd j k = v :=
  pullback.lift_snd _ _ _

/-- The universal lift keeps the actual original arrow. -/
@[reassoc] theorem lift_arrow : lift j k u v a ha hb ≫ arrow j k = a := by
  simp only [lift, arrow, original, Category.assoc, pullback.lift_fst_assoc,
    relationLift_arrow]

variable (e : CategoryTheory.EquivalenceRelation p q)

include e in
/-- Both restricted source endpoints determine the original restricted arrow. -/
theorem hom_ext {x y : T ⟶ relation j k}
    (h₁ : x ≫ fst j k = y ≫ fst j k) (h₂ : x ≫ snd j k = y ≫ snd j k) : x = y := by
  have h : x ≫ original j k = y ≫ original j k := by
    apply relation_hom_ext p q I o e
    · simpa only [Category.assoc, original_first] using congrArg (fun f ↦ f ≫ j) h₁
    · simpa only [Category.assoc, original_second] using congrArg (fun f ↦ f ≫ k) h₂
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [original, Category.assoc] using h
    · simpa only [fst, Category.assoc] using h₁
  · exact h₂

end FLT.Mazur.EquivalenceRelationNormalizedFrames.SourceRestriction
