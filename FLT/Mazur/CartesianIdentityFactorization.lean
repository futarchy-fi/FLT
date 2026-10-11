/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Factorization through a cartesian identity

A cartesian identity forces every map above its test scheme to factor
through the original inclusion. This retains actual morphisms, not just points.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace FLT.Mazur.CartesianIdentity
universe v u
variable {C : Type u} [Category.{v} C] {T X Y Z : C}
  (i : T ⟶ X) (f : X ⟶ Y) (h : IsPullback (𝟙 T) i (i ≫ f) f)

include h

/-- Every map over the cartesian test scheme is its specified original inclusion. -/
theorem factorization (t : Z ⟶ T) (a : Z ⟶ X) (ha : t ≫ (i ≫ f) = a ≫ f) :
    t ≫ i = a := by
  have he : h.lift t a ha = t := by simpa using h.lift_fst t a ha
  rw [← he]
  exact h.lift_snd t a ha

/-- Two maps agreeing downstairs agree if their common map factors through the test. -/
theorem eq_of_factorization (t : Z ⟶ T) (a b : Z ⟶ X)
    (ha : t ≫ (i ≫ f) = a ≫ f) (hab : a ≫ f = b ≫ f) : a = b :=
  (factorization i f h t a ha).symm.trans
    (factorization i f h t b (ha.trans hab))

end FLT.Mazur.CartesianIdentity
