/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedCurvePower

/-!
# Successor decomposition of the actual ordered curve powers

Forgetting the first point gives a cartesian square with the original curve.
The empty power is the unchanged base. These comparisons allow geometric
properties to be proved on the existing wide-pullback parameter schemes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.OrderedCurvePower
variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The actual empty ordered power is canonically the base. -/
def emptyIso : space f 0 ≅ S where
  hom := base f 0
  inv := classify f 0 (𝟙 S) Fin.elim0 (fun i ↦ Fin.elim0 i)
  hom_inv_id := by
    apply hom_ext
    · intro i; exact Fin.elim0 i
    · simp
  inv_hom_id := by simp

/-- Forgetting the first point retains the original wide-pullback objects. -/
def tail (n : ℕ) : space f (n + 1) ⟶ space f n :=
  classify f n (base f (n + 1)) (fun i ↦ point f (n + 1) i.succ)
    (fun i ↦ point_base f (n + 1) i.succ)

@[reassoc (attr := simp)]
lemma tail_point (n : ℕ) (i : Fin n) :
    tail f n ≫ point f n i = point f (n + 1) i.succ := by simp [tail]

@[reassoc (attr := simp)]
lemma tail_base (n : ℕ) : tail f n ≫ base f n = base f (n + 1) := by simp [tail]

/-- Prepending one compatible point constructs the successor tuple. -/
def cons {T : Scheme.{u}} (n : ℕ) (x : T ⟶ X) (a : T ⟶ space f n)
    (h : x ≫ f = a ≫ base f n) : T ⟶ space f (n + 1) :=
  classify f (n + 1) (a ≫ base f n) (Fin.cons x (fun i ↦ a ≫ point f n i))
    (fun i ↦ Fin.cases h (fun j ↦ by simp) i)

@[reassoc (attr := simp)]
lemma cons_zero {T : Scheme.{u}} (n : ℕ) (x : T ⟶ X) (a : T ⟶ space f n)
    (h : x ≫ f = a ≫ base f n) : cons f n x a h ≫ point f (n + 1) 0 = x := by
  simp [cons]

@[reassoc (attr := simp)]
lemma cons_tail {T : Scheme.{u}} (n : ℕ) (x : T ⟶ X) (a : T ⟶ space f n)
    (h : x ≫ f = a ≫ base f n) : cons f n x a h ≫ tail f n = a := by
  apply hom_ext <;> simp [cons]

/-- The successor power is the fiber product of one point and the remaining tuple. -/
theorem successor_isPullback (n : ℕ) :
    IsPullback (point f (n + 1) 0) (tail f n) f (base f n) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (by simp)
    (fun s ↦ cons f n s.fst s.snd s.condition)
    (fun s ↦ cons_zero f n s.fst s.snd s.condition)
    (fun s ↦ cons_tail f n s.fst s.snd s.condition) ?_)
  intro s m hx ha
  apply hom_ext
  · intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa only [cons_zero] using hx
    · have H := congrArg (fun q ↦ q ≫ point f n j) ha
      simpa only [Category.assoc, tail_point, cons, classify_point, Fin.cons_succ] using H
  · have H := congrArg (fun q ↦ q ≫ base f n) ha
    simpa only [Category.assoc, tail_base, cons, classify_base] using H

end FLT.Mazur.OrderedCurvePower
