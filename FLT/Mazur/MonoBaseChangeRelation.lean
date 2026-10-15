/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Base change of a relation along a monomorphism of bases

When both inputs are the actual base changes, their relation over the
original target is already the base change of the original relation.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace FLT.Mazur.MonoBaseChangeRelation
universe u v
variable {C : Type u} [Category.{v} C]
variable {X Y Z S T X' Y' : C}
variable (f : X ⟶ Z) (g : Y ⟶ Z) (z : Z ⟶ S) (b : T ⟶ S) [Mono b]
variable (ix : X' ⟶ X) (sx : X' ⟶ T) (iy : Y' ⟶ Y) (sy : Y' ⟶ T)
variable (hx : IsPullback ix sx (f ≫ z) b) (hy : IsPullback iy sy (g ≫ z) b)
variable [HasPullback f g] [HasPullback (ix ≫ f) (iy ≫ g)]
local notation "P" => pullback f g
local notation "Q" => pullback (ix ≫ f) (iy ≫ g)

/-- The original two projections induce the unchanged relation map. -/
def relationMap : (Q) ⟶ (P) :=
  pullback.map _ _ _ _ ix iy (𝟙 Z) (by simp) (by simp)

include hx hy in
/-- The full relation is the actual base change, including any nonreduced structure. -/
theorem isPullback :
    IsPullback (relationMap f g ix iy) (pullback.fst _ _ ≫ sx)
      (pullback.fst f g ≫ f ≫ z) b := by
  let _ : Mono ix := hx.mono_fst_of_mono
  let _ : Mono iy := hy.mono_fst_of_mono
  refine IsPullback.mk' ?_ ?_ ?_
  · simp only [relationMap, pullback.lift_fst_assoc, Category.assoc, hx.w]
  · intro W u v he _
    apply pullback.hom_ext
    · apply (cancel_mono ix).mp
      have hh := congrArg (fun a ↦ a ≫ pullback.fst f g) he
      simpa only [Category.assoc, relationMap, pullback.lift_fst] using hh
    · apply (cancel_mono iy).mp
      have hh := congrArg (fun a ↦ a ≫ pullback.snd f g) he
      simpa only [Category.assoc, relationMap, pullback.lift_snd] using hh
  · intro W a c he
    let u := hx.lift (a ≫ pullback.fst f g) c (by simpa only [Category.assoc] using he)
    have hv : (a ≫ pullback.snd f g) ≫ g ≫ z = c ≫ b := by
      rw [Category.assoc, ← pullback.condition_assoc]
      exact he
    let v := hy.lift (a ≫ pullback.snd f g) c hv
    have huv : u ≫ ix ≫ f = v ≫ iy ≫ g := by
      rw [← Category.assoc, hx.lift_fst, ← Category.assoc, hy.lift_fst]
      exact Category.assoc _ _ _ |>.trans
        ((congrArg (a ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)
    refine ⟨pullback.lift u v huv, ?_, ?_⟩
    · apply pullback.hom_ext
      · simp only [Category.assoc, relationMap, pullback.lift_fst,
          pullback.lift_fst_assoc, u, hx.lift_fst]
      · simp only [Category.assoc, relationMap, pullback.lift_snd,
          pullback.lift_snd_assoc, v, hy.lift_fst]
    · rw [pullback.lift_fst_assoc, hx.lift_snd]

end FLT.Mazur.MonoBaseChangeRelation
