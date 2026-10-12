/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationSaturationSpan

/-!
# Composition and division of original relative relation arrows

These operations use the original composition pullback, including its independent
base maps. They apply to arbitrary scheme test objects, not only geometric points.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q)
  {T : Scheme.{u}} (a b : T ⟶ A.left)

/-- Compose actual original arrows on any scheme test object. -/
def composeOriginal (h : a ≫ q.left = b ≫ p.left) : T ⟶ A.left :=
  ((IsPullback.of_isLimit e.isLimit).map (Over.forget S)).lift a b h ≫ e.t.left

@[reassoc]
theorem composeOriginal_fst (h : a ≫ q.left = b ≫ p.left) :
    composeOriginal e a b h ≫ p.left = a ≫ p.left := by
  unfold composeOriginal
  rw [Category.assoc, ← Over.comp_left, e.transitivity₁, Over.comp_left,
    ← Category.assoc]
  congr 1
  exact ((IsPullback.of_isLimit e.isLimit).map (Over.forget S)).lift_fst a b h

@[reassoc]
theorem composeOriginal_snd (h : a ≫ q.left = b ≫ p.left) :
    composeOriginal e a b h ≫ q.left = b ≫ q.left := by
  unfold composeOriginal
  rw [Category.assoc, ← Over.comp_left, e.transitivity₂, Over.comp_left,
    ← Category.assoc]
  congr 1
  exact ((IsPullback.of_isLimit e.isLimit).map (Over.forget S)).lift_snd a b h

/-- Arrows with a common target give an original arrow between their sources. -/
def divideOriginal (h : a ≫ q.left = b ≫ q.left) : T ⟶ A.left :=
  composeOriginal e a (b ≫ e.s.left) (by
    rw [Category.assoc, ← Over.comp_left, e.symmetry₁]
    exact h)

@[reassoc]
theorem divideOriginal_fst (h : a ≫ q.left = b ≫ q.left) :
    divideOriginal e a b h ≫ p.left = a ≫ p.left :=
  composeOriginal_fst e _ _ _

@[reassoc]
theorem divideOriginal_snd (h : a ≫ q.left = b ≫ q.left) :
    divideOriginal e a b h ≫ q.left = b ≫ p.left := by
  rw [divideOriginal, composeOriginal_snd, Category.assoc,
    ← Over.comp_left, e.symmetry₂]

end FLT.Mazur.RelativeRelationOrbit
