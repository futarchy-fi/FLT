/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Full overlaps after a fixed base change

An explicitly constructed overlap remains cartesian after base change of
its ambient object. The maps retain both original overlap projections.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace FLT.Mazur.PullbackOverlapBaseChange
universe v u
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {P X Y Z Z' : C} {l : P ⟶ X} {r : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  (H : IsPullback l r f g) (q : Z' ⟶ Z)

/-- The first overlap projection after base change of the ambient object. -/
def first : pullback q (l ≫ f) ⟶ pullback q f :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ l) (by
    rw [Category.assoc, pullback.condition])

/-- The second overlap projection after the same base change. -/
def second : pullback q (l ≫ f) ⟶ pullback q g :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ r) (by
    rw [Category.assoc, ← H.w, pullback.condition])

/-- The first projection preserves the extended ambient coordinate. -/
@[reassoc] theorem first_fst : first (l := l) (f := f) q ≫ pullback.fst q f =
    pullback.fst q (l ≫ f) := pullback.lift_fst _ _ _

/-- The first projection preserves the original overlap coordinate. -/
@[reassoc] theorem first_snd : first (l := l) (f := f) q ≫ pullback.snd q f =
    pullback.snd q (l ≫ f) ≫ l := pullback.lift_snd _ _ _

/-- The second projection preserves the extended ambient coordinate. -/
@[reassoc] theorem second_fst : second H q ≫ pullback.fst q g =
    pullback.fst q (l ≫ f) := pullback.lift_fst _ _ _

/-- The second projection preserves the original overlap coordinate. -/
@[reassoc] theorem second_snd : second H q ≫ pullback.snd q g =
    pullback.snd q (l ≫ f) ≫ r := pullback.lift_snd _ _ _

/-- The two extended projections agree over the new ambient object. -/
theorem condition : first (l := l) (f := f) q ≫ pullback.fst q f =
    second H q ≫ pullback.fst q g := by rw [first_fst, second_fst]

/-- Every compatible pair of extended chart maps lifts into the full extended overlap. -/
theorem exists_lift {T : C} (x : T ⟶ pullback q f) (y : T ⟶ pullback q g)
    (hxy : x ≫ pullback.fst q f = y ≫ pullback.fst q g) :
    ∃ t : T ⟶ pullback q (l ≫ f),
      t ≫ first (l := l) (f := f) q = x ∧ t ≫ second H q = y := by
  have hw : (x ≫ pullback.snd q f) ≫ f = (y ≫ pullback.snd q g) ≫ g := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hxy,
      Category.assoc, pullback.condition, ← Category.assoc]
  let t := H.lift (x ≫ pullback.snd q f) (y ≫ pullback.snd q g) hw
  have ht : (x ≫ pullback.fst q f) ≫ q = t ≫ (l ≫ f) := by
    dsimp only [t]
    rw [H.lift_fst_assoc, Category.assoc, pullback.condition, ← Category.assoc]
  refine ⟨pullback.lift (x ≫ pullback.fst q f) t ht, ?_, ?_⟩
  · apply pullback.hom_ext
    · simp only [Category.assoc, first_fst, pullback.lift_fst]
    · simp only [Category.assoc, first_snd, pullback.lift_snd_assoc, t, H.lift_fst]
  · apply pullback.hom_ext
    · simpa only [Category.assoc, second_fst, pullback.lift_fst] using hxy
    · simp only [Category.assoc, second_snd, pullback.lift_snd_assoc, t, H.lift_snd]

/-- The two extended overlap projections jointly determine every test-scheme morphism. -/
theorem hom_ext {T : C} {x y : T ⟶ pullback q (l ≫ f)}
    (h₁ : x ≫ first (l := l) (f := f) q = y ≫ first (l := l) (f := f) q)
    (h₂ : x ≫ second H q = y ≫ second H q) : x = y := by
  apply pullback.hom_ext
  · simpa only [Category.assoc, first_fst] using
      congrArg (fun t => t ≫ pullback.fst q f) h₁
  · apply H.hom_ext
    · simpa only [Category.assoc, first_snd] using
        congrArg (fun t => t ≫ pullback.snd q f) h₁
    · simpa only [Category.assoc, second_snd] using
        congrArg (fun t => t ≫ pullback.snd q g) h₂

/-- Base change preserves the full constructed overlap, including its universal property. -/
theorem isPullback : IsPullback (first (l := l) (f := f) q) (second H q)
    (pullback.fst q f) (pullback.fst q g) := by
  have h (s : PullbackCone (pullback.fst q f) (pullback.fst q g)) :=
    exists_lift H q s.fst s.snd s.condition
  choose lift hl hr using h
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (condition H q) lift hl hr ?_)
  intro s t ht₁ ht₂
  exact hom_ext H q (ht₁.trans (hl s).symm) (ht₂.trans (hr s).symm)

end FLT.Mazur.PullbackOverlapBaseChange
