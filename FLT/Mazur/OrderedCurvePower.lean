/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks

/-!
# Ordered points on a relative curve

The finite wide pullback represents ordered tuples of points over the base,
including the empty tuple. No smoothness assumption is needed for this construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.OrderedCurvePower

variable {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)

/-- The actual scheme of ordered `n`-tuples over the common base. -/
abbrev space : Scheme.{u} := widePullback S (fun _ : Fin n ↦ X) (fun _ ↦ f)

/-- The common structural map, also defined when the tuple is empty. -/
abbrev base : space f n ⟶ S := WidePullback.base (fun _ : Fin n ↦ f)

/-- Evaluation at one entry of the ordered tuple. -/
abbrev point (i : Fin n) : space f n ⟶ X := WidePullback.π (fun _ : Fin n ↦ f) i

@[reassoc]
lemma point_base (i : Fin n) : point f n i ≫ f = base f n := WidePullback.π_arrow _ i

/-- The classifying map of an actual ordered tuple over `g`. -/
def classify {T : Scheme.{u}} (g : T ⟶ S) (x : Fin n → (T ⟶ X))
    (hx : ∀ i, x i ≫ f = g) : T ⟶ space f n := WidePullback.lift g x hx

@[reassoc (attr := simp)]
lemma classify_point {T : Scheme.{u}} (g : T ⟶ S) (x : Fin n → (T ⟶ X))
    (hx : ∀ i, x i ≫ f = g) (i : Fin n) : classify f n g x hx ≫ point f n i = x i :=
  WidePullback.lift_π _ _ _ _ _

@[reassoc (attr := simp)]
lemma classify_base {T : Scheme.{u}} (g : T ⟶ S) (x : Fin n → (T ⟶ X))
    (hx : ∀ i, x i ≫ f = g) : classify f n g x hx ≫ base f n = g :=
  WidePullback.lift_base _ _ _ _

/-- Maps are determined by the base map and all their ordered entries. -/
@[ext]
lemma hom_ext {T : Scheme.{u}} {a b : T ⟶ space f n}
    (hp : ∀ i, a ≫ point f n i = b ≫ point f n i)
    (hb : a ≫ base f n = b ≫ base f n) : a = b := WidePullback.hom_ext _ a b hp hb

/-- The representing equivalence for ordered tuples, with no supplied representative. -/
def pointsEquiv {T : Scheme.{u}} (g : T ⟶ S) :
    {a : T ⟶ space f n // a ≫ base f n = g} ≃
      {x : Fin n → (T ⟶ X) // ∀ i, x i ≫ f = g} where
  toFun a := ⟨fun i ↦ a.1 ≫ point f n i, by simp [a.2]⟩
  invFun x := ⟨classify f n g x.1 x.2, classify_base _ _ _ _ _⟩
  left_inv a := by apply Subtype.ext; apply hom_ext <;> simp [a.2]
  right_inv x := by apply Subtype.ext; funext i; simp

/-- Classifying ordered tuples commutes with change of the test scheme. -/
lemma classify_precomp {T U : Scheme.{u}} (g : T ⟶ S) (x : Fin n → (T ⟶ X))
    (hx : ∀ i, x i ≫ f = g) (a : U ⟶ T) :
    a ≫ classify f n g x hx =
      classify f n (a ≫ g) (fun i ↦ a ≫ x i) (by simp [hx]) := by
  apply hom_ext <;> simp

end FLT.Mazur.OrderedCurvePower
