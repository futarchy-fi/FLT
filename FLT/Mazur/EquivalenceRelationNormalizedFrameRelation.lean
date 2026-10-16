/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedFrameEtale

/-!
# The full original relation pulled back to normalized frames

Two independent normalized frames are related by an arbitrary original arrow.
The representing scheme uses two actual pullbacks of the entire original
relation, preserving both endpoints and its original scheme structure.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} (p q : D ⟶ A) [IsSeparated p]
  (I : Type) [Fintype I] (o : I)

/-- The full original relation with its first endpoint lifted to a normalized frame. -/
def leftRelation : Scheme := pullback (first p q I o) p

/-- The unchanged second original endpoint on the first pullback. -/
def leftRelationTarget : leftRelation p q I o ⟶ A :=
  pullback.snd (first p q I o) p ≫ q

/-- Both independent normalized endpoints of the entire original relation. -/
def fullRelation : Scheme := pullback (leftRelationTarget p q I o) (first p q I o)

/-- The independent first normalized frame. -/
def relationFirst : fullRelation p q I o ⟶ source p q I o :=
  pullback.fst _ _ ≫ pullback.fst (first p q I o) p

/-- The independent second normalized frame. -/
def relationSecond : fullRelation p q I o ⟶ source p q I o := pullback.snd _ _

/-- The actual original relation arrow, with no branch restriction. -/
def relationArrow : fullRelation p q I o ⟶ D :=
  pullback.fst _ _ ≫ pullback.snd (first p q I o) p

/-- The original arrow starts at the original first endpoint. -/
@[reassoc] theorem relationArrow_first :
    relationArrow p q I o ≫ p = relationFirst p q I o ≫ first p q I o := by
  simp only [relationArrow, relationFirst, Category.assoc, pullback.condition]

/-- The original arrow ends at the independent original second endpoint. -/
@[reassoc] theorem relationArrow_second :
    relationArrow p q I o ≫ q = relationSecond p q I o ≫ first p q I o := by
  exact (Category.assoc _ _ _).trans pullback.condition

/-- Both full relation endpoints retain every original equalized coefficient morphism. -/
@[reassoc] theorem relation_coefficients {S : Scheme} (c : A ⟶ S)
    (hc : p ≫ c = q ≫ c) :
    relationFirst p q I o ≫ first p q I o ≫ c =
      relationSecond p q I o ≫ first p q I o ≫ c := by
  rw [← Category.assoc, ← relationArrow_first, Category.assoc, hc,
    ← Category.assoc, relationArrow_second, Category.assoc]

variable {T : Scheme} (u v : T ⟶ source p q I o) (a : T ⟶ D)
  (ha : a ≫ p = u ≫ first p q I o) (hb : a ≫ q = v ≫ first p q I o)

/-- Every original related pair lifts to the full scheme relation. -/
def relationLift : T ⟶ fullRelation p q I o :=
  pullback.lift (pullback.lift u a ha.symm) v (by
    rw [leftRelationTarget, ← Category.assoc, pullback.lift_snd]
    exact hb)

/-- Lifting keeps the first normalized frame. -/
@[reassoc] theorem relationLift_first :
    relationLift p q I o u v a ha hb ≫ relationFirst p q I o = u := by
  simp only [relationLift, relationFirst, ← Category.assoc,
    pullback.lift_fst]

/-- Lifting keeps the second normalized frame. -/
@[reassoc] theorem relationLift_second :
    relationLift p q I o u v a ha hb ≫ relationSecond p q I o = v :=
  pullback.lift_snd _ _ _

/-- Lifting keeps the entire original relation arrow. -/
@[reassoc] theorem relationLift_arrow :
    relationLift p q I o u v a ha hb ≫ relationArrow p q I o = a := by
  simp only [relationLift, relationArrow, ← Category.assoc,
    pullback.lift_fst, pullback.lift_snd]

variable (e : CategoryTheory.EquivalenceRelation p q)

include e in
/-- The two independent endpoints determine maps into the full original relation. -/
theorem relation_hom_ext {x y : T ⟶ fullRelation p q I o}
    (h₁ : x ≫ relationFirst p q I o = y ≫ relationFirst p q I o)
    (h₂ : x ≫ relationSecond p q I o = y ≫ relationSecond p q I o) : x = y := by
  have ha : x ≫ relationArrow p q I o = y ≫ relationArrow p q I o := by
    apply e.right_cancellation
    · simpa only [Category.assoc, relationArrow_first] using
        congrArg (fun f ↦ f ≫ first p q I o) h₁
    · simpa only [Category.assoc, relationArrow_second] using
        congrArg (fun f ↦ f ≫ first p q I o) h₂
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans (h₁.trans (Category.assoc _ _ _).symm)
    · exact (Category.assoc _ _ _).trans (ha.trans (Category.assoc _ _ _).symm)
  · exact h₂

variable [Etale p]

include e in
/-- The first projection of the full relation on normalized frames is etale. -/
theorem relationFirst_etale : Etale (relationFirst p q I o) := by
  let _ := first_etale e I o
  change Etale (pullback.fst (leftRelationTarget p q I o) (first p q I o) ≫
    pullback.fst (first p q I o) p)
  infer_instance

end FLT.Mazur.EquivalenceRelationNormalizedFrames
