/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.CartesianCoefficientTransport

/-!
# The coefficient Cech comparison is the original object's kernel pair

For a cartesian coefficient model, the actual overlap transport and the first
projection give the full kernel pair of the original-object projection.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace FLT.Mazur.CartesianCoefficientTransport
universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {B S X Y : C} {p : Y ⟶ X} {s : Y ⟶ S} {f : X ⟶ B} {q : S ⟶ B}
  (H : IsPullback p s f q)
local notation "a" => pullback.fst q q
local notation "b" => pullback.snd q q
local notation "first" => pullback.snd a s
local notation "second" => map H a b pullback.condition ≫ pullback.snd b s

/-- The genuine coefficient overlap, with its transport, is the full original kernel pair. -/
theorem cech_isPullback : IsPullback first second p p := by
  have compat (c : PullbackCone p p) :
      (c.fst ≫ s) ≫ q = (c.snd ≫ s) ≫ q := by
    rw [Category.assoc, ← H.w, ← Category.assoc, c.condition,
      Category.assoc, H.w, Category.assoc]
  let pair (c : PullbackCone p p) :=
    pullback.lift (c.fst ≫ s) (c.snd ≫ s) (compat c)
  let lift (c : PullbackCone p p) : c.pt ⟶ pullback a s :=
    pullback.lift (pair c) c.fst (pullback.lift_fst _ _ _)
  have hl (c : PullbackCone p p) : lift c ≫ first = c.fst := pullback.lift_snd _ _ _
  have hr (c : PullbackCone p p) : lift c ≫ second = c.snd := by
    apply H.hom_ext
    · simp only [Category.assoc, map_original]
      rw [← Category.assoc, hl, c.condition]
    · simp only [Category.assoc, ← pullback.condition (f := b) (g := s),
        map_coefficient_assoc]
      dsimp only [lift, pair]
      rw [pullback.lift_fst_assoc, pullback.lift_snd]
  have hw : first ≫ p = second ≫ p := by
    simpa only [Category.assoc] using (map_original H a b pullback.condition).symm
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw lift hl hr ?_)
  intro c m hm hn
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · calc
        (m ≫ pullback.fst a s) ≫ a = (m ≫ first) ≫ s := by
          simp only [Category.assoc, pullback.condition]
        _ = c.fst ≫ s := congrArg (· ≫ s) hm
        _ = (lift c ≫ pullback.fst a s) ≫ a := by
          simp only [lift, pair, pullback.lift_fst]
    · calc
        (m ≫ pullback.fst a s) ≫ b = (m ≫ second) ≫ s := by
          simp only [Category.assoc, ← pullback.condition (f := b) (g := s),
            map_coefficient_assoc]
        _ = c.snd ≫ s := congrArg (· ≫ s) hn
        _ = (lift c ≫ pullback.fst a s) ≫ b := by
          simp only [lift, pair, Category.assoc, pullback.lift_fst_assoc,
            pullback.lift_snd]
  · exact hm.trans (hl c).symm

end FLT.Mazur.CartesianCoefficientTransport
