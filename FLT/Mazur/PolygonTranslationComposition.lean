/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonActionTranslation

/-!
# Composition of the actual full-polygon translations

The universal-action specializations multiply their original unit parameters
and add their original component labels on the entire singular curve.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonActionTranslation
open PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] translation polygonScaling polygonRotation
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- The identity unit and zero label give the identity of the original complete polygon. -/
theorem translation_one_zero : translation K n hn p q h 1 0 = 𝟙 C := by
  rw [translation_eq, polygonScaling_one, polygonRotation_zero, Category.id_comp]

/-- Composition multiplies units and adds labels without restricting to the smooth locus. -/
theorem translation_mul_add (c d : Kˣ) (b e : ZMod n) :
    translation K n hn p q h c b ≫ translation K n hn p q h d e =
      translation K n hn p q h (c * d) (b + e) := by
  simp only [translation_eq, Category.assoc]
  rw [← Category.assoc (polygonRotation K hn p q h b),
    ← polygonScaling_rotation, Category.assoc,
    ← polygonRotation_add, ← Category.assoc, ← polygonScaling_mul]

/-- The same composition equation on the actual underlying schemes. -/
theorem translation_mul_add_left (c d : Kˣ) (b e : ZMod n) :
    (translation K n hn p q h c b).left ≫ (translation K n hn p q h d e).left =
      (translation K n hn p q h (c * d) (b + e)).left :=
  congrArg Over.Hom.left (translation_mul_add K n hn p q h c d b e)

end FLT.Mazur.PolygonActionTranslation
