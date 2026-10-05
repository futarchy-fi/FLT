/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOverlapBaseChange
public import FLT.Mazur.SchemeOverlapCocycleChart
public import FLT.Mazur.SchemeOverlapRefinement

/-!
# Cocycle preservation on a refined triple-overlap test scheme

A commutative projection square restricts an overlap to a pulled-back sheaf.
If the original overlap has its cocycle on the composite pair maps from a
specified refined triple test scheme, the restricted overlap has its cocycle
there too. Producing those composite pair maps remains a geometric obligation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeOverlapRefinementCocycle
open SchemeOverlapDiagonalChart SchemeOverlapCocycleChart SchemeOverlapBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Y Y' Z Z' T : Scheme.{u}}

/-- Restrict a double-overlap isomorphism along a commutative projection square. -/
def restrict (l r : Z ⟶ Y) (l' r' : Z' ⟶ Y') (b : Y' ⟶ Y) (k : Z' ⟶ Z)
    (wl : k ≫ l = l' ≫ b) (wr : k ≫ r = r' ≫ b) (M : Y.Modules)
    (e : (pullback l).obj M ≅ (pullback r).obj M) :=
  baseChange l' r' b M (normalize l r k (l' ≫ b) (r' ≫ b) wl wr M e)

/-- Restriction preserves a cocycle tested on the composite pair maps. -/
theorem restrict_cocycle (l r : Z ⟶ Y) (l' r' : Z' ⟶ Y') (b : Y' ⟶ Y) (k : Z' ⟶ Z)
    (wl : k ≫ l = l' ≫ b) (wr : k ≫ r = r' ≫ b)
    (q12 q23 q13 : T ⟶ Z') (c1 c2 c3 : T ⟶ Y')
    (w12l : q12 ≫ l' = c1) (w12r : q12 ≫ r' = c2)
    (w23l : q23 ≫ l' = c2) (w23r : q23 ≫ r' = c3)
    (w13l : q13 ≫ l' = c1) (w13r : q13 ≫ r' = c3)
    (u12l : (q12 ≫ k) ≫ l = c1 ≫ b) (u12r : (q12 ≫ k) ≫ r = c2 ≫ b)
    (u23l : (q23 ≫ k) ≫ l = c2 ≫ b) (u23r : (q23 ≫ k) ≫ r = c3 ≫ b)
    (u13l : (q13 ≫ k) ≫ l = c1 ≫ b) (u13r : (q13 ≫ k) ≫ r = c3 ≫ b)
    (M : Y.Modules) (e : (pullback l).obj M ≅ (pullback r).obj M)
    (h : CocycleCompatible l r (q12 ≫ k) (q23 ≫ k) (q13 ≫ k)
      (c1 ≫ b) (c2 ≫ b) (c3 ≫ b) u12l u12r u23l u23r u13l u13r M e) :
    CocycleCompatible l' r' q12 q23 q13 c1 c2 c3 w12l w12r w23l w23r w13l w13r
      ((pullback b).obj M) (restrict l r l' r' b k wl wr M e) := by
  have v12l : q12 ≫ (l' ≫ b) = c1 ≫ b := by rw [← Category.assoc, w12l]
  have v12r : q12 ≫ (r' ≫ b) = c2 ≫ b := by rw [← Category.assoc, w12r]
  have v23l : q23 ≫ (l' ≫ b) = c2 ≫ b := by rw [← Category.assoc, w23l]
  have v23r : q23 ≫ (r' ≫ b) = c3 ≫ b := by rw [← Category.assoc, w23r]
  have v13l : q13 ≫ (l' ≫ b) = c1 ≫ b := by rw [← Category.assoc, w13l]
  have v13r : q13 ≫ (r' ≫ b) = c3 ≫ b := by rw [← Category.assoc, w13r]
  have hc := (normalize_cocycle_iff l r (q12 ≫ k) (q23 ≫ k) (q13 ≫ k)
    (c1 ≫ b) (c2 ≫ b) (c3 ≫ b) u12l u12r u23l u23r u13l u13r M e
    k (l' ≫ b) (r' ≫ b) wl wr q12 q23 q13 rfl rfl rfl
    v12l v12r v23l v23r v13l v13r).mpr h
  unfold CocycleCompatible restrict
  rw [normalize_baseChange l' r' b q12 c1 c2 w12l w12r v12l v12r,
    normalize_baseChange l' r' b q23 c2 c3 w23l w23r v23l v23r,
    normalize_baseChange l' r' b q13 c1 c3 w13l w13r v13l v13r]
  exact baseChange_hom_comp c1 c2 c3 b M _ _ _ hc

/-- On categorical double overlaps the projection-square restriction is the existing refinement. -/
theorem restrict_eq_refine {X X' : Scheme.{u}} (p : Y ⟶ X) (q : Y' ⟶ X')
    (a : X' ⟶ X) (b : Y' ⟶ Y) (w : q ≫ a = b ≫ p) (M : Y.Modules)
    (e : (pullback (Limits.pullback.fst p p)).obj M ≅
      (pullback (Limits.pullback.snd p p)).obj M) :
    restrict (Limits.pullback.fst p p) (Limits.pullback.snd p p)
      (Limits.pullback.fst q q) (Limits.pullback.snd q q) b
      (SchemeOverlapRefinement.overlapMap p q a b w)
      (SchemeOverlapRefinement.overlapMap_fst p q a b w)
      (SchemeOverlapRefinement.overlapMap_snd p q a b w) M e =
    SchemeOverlapRefinement.refine p q a b w e := by
  apply Iso.ext
  simp only [restrict, baseChange, SchemeOverlapDiagonalChart.normalize,
    SheafPullbackPathComparison.comparison, SchemeOverlapRefinement.refine,
    SchemeOverlapRefinement.firstIso, SchemeOverlapRefinement.secondIso,
    Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv, Iso.trans_inv,
    NatTrans.comp_app, Category.assoc, pullbackCongr, eqToIso]

end FLT.Mazur.SchemeOverlapRefinementCocycle
