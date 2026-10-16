/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedFrameRelation

/-!
# The full original relation between independently indexed frames

The two endpoints may have different finite label types and different
distinguished labels. Both pullbacks use the entire original relation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} (p q : D ⟶ A) [IsSeparated p]
  (I J : Type) [Fintype I] [Fintype J] (o : I) (o' : J)

/-- The second normalized frame is independent in both its size and its label. -/
def relation : Scheme := pullback (leftRelationTarget p q I o) (first p q J o')

/-- The first independent frame of the full mixed relation. -/
def fst : relation p q I J o o' ⟶ source p q I o :=
  pullback.fst _ _ ≫ pullback.fst (first p q I o) p

/-- The second independent frame of the full mixed relation. -/
def snd : relation p q I J o o' ⟶ source p q J o' := pullback.snd _ _

/-- The unchanged original arrow of the full mixed relation. -/
def arrow : relation p q I J o o' ⟶ D :=
  pullback.fst _ _ ≫ pullback.snd (first p q I o) p

/-- The original arrow starts at the first frame's actual original endpoint. -/
@[reassoc] theorem arrow_first :
    arrow p q I J o o' ≫ p = fst p q I J o o' ≫ first p q I o := by
  simp only [arrow, fst, Category.assoc, pullback.condition]

/-- The original arrow ends at the second frame's actual original endpoint. -/
@[reassoc] theorem arrow_second :
    arrow p q I J o o' ≫ q = snd p q I J o o' ≫ first p q J o' :=
  (Category.assoc _ _ _).trans pullback.condition

/-- Every original equalized coefficient survives the independently indexed pullbacks. -/
@[reassoc] theorem coefficients {S : Scheme} (c : A ⟶ S) (hc : p ≫ c = q ≫ c) :
    fst p q I J o o' ≫ first p q I o ≫ c =
      snd p q I J o o' ≫ first p q J o' ≫ c := by
  rw [← Category.assoc, ← arrow_first, Category.assoc, hc,
    ← Category.assoc, arrow_second, Category.assoc]

variable {T : Scheme} (u : T ⟶ source p q I o) (v : T ⟶ source p q J o')
  (a : T ⟶ D) (ha : a ≫ p = u ≫ first p q I o) (hb : a ≫ q = v ≫ first p q J o')

/-- Every original arrow with the two prescribed frames has its actual mixed relation lift. -/
def lift : T ⟶ relation p q I J o o' :=
  pullback.lift (pullback.lift u a ha.symm) v (by
    rw [leftRelationTarget, ← Category.assoc, pullback.lift_snd]
    exact hb)

/-- Lifting retains the first independently indexed frame. -/
@[reassoc] theorem lift_fst : lift p q I J o o' u v a ha hb ≫ fst p q I J o o' = u := by
  simp only [lift, fst, pullback.lift_fst_assoc, pullback.lift_fst]

/-- Lifting retains the second independently indexed frame. -/
@[reassoc] theorem lift_snd : lift p q I J o o' u v a ha hb ≫ snd p q I J o o' = v :=
  pullback.lift_snd _ _ _

/-- Lifting retains the original arrow, with all of its scheme structure. -/
@[reassoc] theorem lift_arrow : lift p q I J o o' u v a ha hb ≫ arrow p q I J o o' = a := by
  simp only [lift, arrow, pullback.lift_fst_assoc, pullback.lift_snd]

variable (e : CategoryTheory.EquivalenceRelation p q)

include e in
/-- The two independently indexed frames determine a mixed relation map. -/
theorem hom_ext {x y : T ⟶ relation p q I J o o'}
    (h₁ : x ≫ fst p q I J o o' = y ≫ fst p q I J o o')
    (h₂ : x ≫ snd p q I J o o' = y ≫ snd p q I J o o') : x = y := by
  have ha : x ≫ arrow p q I J o o' = y ≫ arrow p q I J o o' := by
    apply e.right_cancellation
    · simpa only [Category.assoc, arrow_first] using
        congrArg (fun f ↦ f ≫ first p q I o) h₁
    · simpa only [Category.assoc, arrow_second] using
        congrArg (fun f ↦ f ≫ first p q J o') h₂
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [fst, Category.assoc] using h₁
    · simpa only [arrow, Category.assoc] using ha
  · exact h₂

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
