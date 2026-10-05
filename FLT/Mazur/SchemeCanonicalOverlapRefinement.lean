/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOverlapConjugation
public import FLT.Mazur.SchemeOverlapRefinementCocycle
public import FLT.Mazur.SchemeReconstructionOverlapSquare

/-!
# Refinement preserves canonical categorical overlaps

The actual refinement map of categorical fiber products transports a canonical
reconstruction overlap to the canonical overlap of the restricted reconstruction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeOverlapRefinement
open SchemePullbackOverlap SchemeOverlapRefinementCocycle
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y X' Y' : Scheme.{u}}
variable (p : Y ⟶ X) (q : Y' ⟶ X') (a : X' ⟶ X) (b : Y' ⟶ Y)
variable (w : q ≫ a = b ≫ p)

/-- The actual categorical refinement preserves canonical reconstruction overlaps. -/
theorem refine_chartOverlap (k : Limits.pullback p p ⟶ X)
    (hl : Limits.pullback.fst p p ≫ p = k) (hr : Limits.pullback.snd p p ≫ p = k)
    (k' : Limits.pullback q q ⟶ X')
    (hl' : Limits.pullback.fst q q ≫ q = k') (hr' : Limits.pullback.snd q q ≫ q = k')
    (A : X.Modules) {M : Y.Modules} (e : (pullback p).obj A ≅ M) :
    refine p q a b w
        (chartOverlap p (Limits.pullback.fst p p) (Limits.pullback.snd p p) k hl hr A e) =
      chartOverlap q (Limits.pullback.fst q q) (Limits.pullback.snd q q) k' hl' hr'
        ((pullback a).obj A)
        ((SchemePullbackSquare.squareIso p q a b w).app A ≪≫ (pullback b).mapIso e) := by
  have hfl : (Limits.pullback.fst q q ≫ b) ≫ p = k' ≫ a := by
    rw [Category.assoc, ← w, ← Category.assoc, hl']
  have hfr : (Limits.pullback.snd q q ≫ b) ≫ p = k' ≫ a := by
    rw [Category.assoc, ← w, ← Category.assoc, hr']
  have hk : overlapMap p q a b w ≫ k = k' ≫ a := by
    rw [← hl, ← Category.assoc, overlapMap_fst]
    exact hfl
  rw [← restrict_eq_refine]
  unfold SchemeOverlapRefinementCocycle.restrict
  rw [normalize_chartOverlap p _ _ k hl hr _ _ _
    (overlapMap_fst p q a b w) (overlapMap_snd p q a b w)
    (hfl.trans hk.symm) (hfr.trans hk.symm)]
  simp only [hk]
  exact baseChange_chartOverlap_square p q a b w _ _ k' hl' hr' hfl hfr A e

end FLT.Mazur.SchemeOverlapRefinement
