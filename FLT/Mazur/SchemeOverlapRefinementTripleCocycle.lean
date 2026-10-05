/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOverlapRefinementCocycle
public import FLT.Mazur.SchemeOverlapCocyclePullback

/-!
# Cocycle restriction along a triple-overlap square

Commuting coordinate and pair squares transport the original triple-overlap
cocycle to the restricted overlap. No refined cocycle is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeOverlapRefinementCocycle
open SchemeOverlapCocycleChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Y Y' Z Z' T T' : Scheme.{u}}

/-- Restriction preserves cocycles when the triple-overlap squares commute. -/
theorem restrict_cocycle_of_squares (l r : Z ⟶ Y) (l' r' : Z' ⟶ Y')
    (b : Y' ⟶ Y) (k : Z' ⟶ Z) (wl : k ≫ l = l' ≫ b) (wr : k ≫ r = r' ≫ b)
    (p12 p23 p13 : T ⟶ Z) (c1 c2 c3 : T ⟶ Y)
    (w12l : p12 ≫ l = c1) (w12r : p12 ≫ r = c2)
    (w23l : p23 ≫ l = c2) (w23r : p23 ≫ r = c3)
    (w13l : p13 ≫ l = c1) (w13r : p13 ≫ r = c3)
    (q12 q23 q13 : T' ⟶ Z') (d1 d2 d3 : T' ⟶ Y')
    (v12l : q12 ≫ l' = d1) (v12r : q12 ≫ r' = d2)
    (v23l : q23 ≫ l' = d2) (v23r : q23 ≫ r' = d3)
    (v13l : q13 ≫ l' = d1) (v13r : q13 ≫ r' = d3)
    (t : T' ⟶ T) (s1 : t ≫ c1 = d1 ≫ b) (s2 : t ≫ c2 = d2 ≫ b)
    (s3 : t ≫ c3 = d3 ≫ b)
    (s12 : t ≫ p12 = q12 ≫ k) (s23 : t ≫ p23 = q23 ≫ k)
    (s13 : t ≫ p13 = q13 ≫ k)
    (M : Y.Modules) (e : (pullback l).obj M ≅ (pullback r).obj M)
    (h : CocycleCompatible l r p12 p23 p13 c1 c2 c3
      w12l w12r w23l w23r w13l w13r M e) :
    CocycleCompatible l' r' q12 q23 q13 d1 d2 d3 v12l v12r v23l v23r v13l v13r
      ((pullback b).obj M) (restrict l r l' r' b k wl wr M e) := by
  have u12l : (t ≫ p12) ≫ l = d1 ≫ b := by rw [Category.assoc, w12l, s1]
  have u12r : (t ≫ p12) ≫ r = d2 ≫ b := by rw [Category.assoc, w12r, s2]
  have u23l : (t ≫ p23) ≫ l = d2 ≫ b := by rw [Category.assoc, w23l, s2]
  have u23r : (t ≫ p23) ≫ r = d3 ≫ b := by rw [Category.assoc, w23r, s3]
  have u13l : (t ≫ p13) ≫ l = d1 ≫ b := by rw [Category.assoc, w13l, s1]
  have u13r : (t ≫ p13) ≫ r = d3 ≫ b := by rw [Category.assoc, w13r, s3]
  have hc := pullback_cocycle l r p12 p23 p13 c1 c2 c3
    w12l w12r w23l w23r w13l w13r M e t (d1 ≫ b) (d2 ≫ b) (d3 ≫ b)
    s1 s2 s3 u12l u12r u23l u23r u13l u13r h
  have z12l : (q12 ≫ k) ≫ l = d1 ≫ b := by rw [← s12]; exact u12l
  have z12r : (q12 ≫ k) ≫ r = d2 ≫ b := by rw [← s12]; exact u12r
  have z23l : (q23 ≫ k) ≫ l = d2 ≫ b := by rw [← s23]; exact u23l
  have z23r : (q23 ≫ k) ≫ r = d3 ≫ b := by rw [← s23]; exact u23r
  have z13l : (q13 ≫ k) ≫ l = d1 ≫ b := by rw [← s13]; exact u13l
  have z13r : (q13 ≫ k) ≫ r = d3 ≫ b := by rw [← s13]; exact u13r
  apply restrict_cocycle l r l' r' b k wl wr q12 q23 q13 d1 d2 d3
    v12l v12r v23l v23r v13l v13r z12l z12r z23l z23r z13l z13r M e
  simpa only [s12, s23, s13] using hc

/-- Categorical overlap refinement preserves cocycles along a triple-overlap square. -/
theorem refine_cocycle_of_squares {X X' : Scheme.{u}}
    (p : Y ⟶ X) (q : Y' ⟶ X') (a : X' ⟶ X) (b : Y' ⟶ Y)
    (w : q ≫ a = b ≫ p)
    (p12 p23 p13 : T ⟶ Limits.pullback p p) (c1 c2 c3 : T ⟶ Y)
    (w12l : p12 ≫ Limits.pullback.fst p p = c1)
    (w12r : p12 ≫ Limits.pullback.snd p p = c2)
    (w23l : p23 ≫ Limits.pullback.fst p p = c2)
    (w23r : p23 ≫ Limits.pullback.snd p p = c3)
    (w13l : p13 ≫ Limits.pullback.fst p p = c1)
    (w13r : p13 ≫ Limits.pullback.snd p p = c3)
    (q12 q23 q13 : T' ⟶ Limits.pullback q q) (d1 d2 d3 : T' ⟶ Y')
    (v12l : q12 ≫ Limits.pullback.fst q q = d1)
    (v12r : q12 ≫ Limits.pullback.snd q q = d2)
    (v23l : q23 ≫ Limits.pullback.fst q q = d2)
    (v23r : q23 ≫ Limits.pullback.snd q q = d3)
    (v13l : q13 ≫ Limits.pullback.fst q q = d1)
    (v13r : q13 ≫ Limits.pullback.snd q q = d3)
    (t : T' ⟶ T) (s1 : t ≫ c1 = d1 ≫ b) (s2 : t ≫ c2 = d2 ≫ b)
    (s3 : t ≫ c3 = d3 ≫ b)
    (s12 : t ≫ p12 = q12 ≫ SchemeOverlapRefinement.overlapMap p q a b w)
    (s23 : t ≫ p23 = q23 ≫ SchemeOverlapRefinement.overlapMap p q a b w)
    (s13 : t ≫ p13 = q13 ≫ SchemeOverlapRefinement.overlapMap p q a b w)
    (M : Y.Modules)
    (e : (pullback (Limits.pullback.fst p p)).obj M ≅
      (pullback (Limits.pullback.snd p p)).obj M)
    (h : CocycleCompatible (Limits.pullback.fst p p) (Limits.pullback.snd p p)
      p12 p23 p13 c1 c2 c3 w12l w12r w23l w23r w13l w13r M e) :
    CocycleCompatible (Limits.pullback.fst q q) (Limits.pullback.snd q q)
      q12 q23 q13 d1 d2 d3 v12l v12r v23l v23r v13l v13r
      ((pullback b).obj M) (SchemeOverlapRefinement.refine p q a b w e) := by
  simpa only [restrict_eq_refine] using restrict_cocycle_of_squares
    (Limits.pullback.fst p p) (Limits.pullback.snd p p)
    (Limits.pullback.fst q q) (Limits.pullback.snd q q) b
    (SchemeOverlapRefinement.overlapMap p q a b w)
    (SchemeOverlapRefinement.overlapMap_fst p q a b w)
    (SchemeOverlapRefinement.overlapMap_snd p q a b w)
    p12 p23 p13 c1 c2 c3 w12l w12r w23l w23r w13l w13r
    q12 q23 q13 d1 d2 d3 v12l v12r v23l v23r v13l v13r
    t s1 s2 s3 s12 s23 s13 M e h

end FLT.Mazur.SchemeOverlapRefinementCocycle
