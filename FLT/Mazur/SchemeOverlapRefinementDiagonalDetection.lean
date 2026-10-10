/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOverlapRefinementDiagonal

/-!
# Detecting the pullback of a diagonal law on a refinement

The diagonal law of a refined overlap implies the pullback of the original
law to that source chart. A covering family can therefore detect the law.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeOverlapRefinement
open SchemeModulePullbackUnits SchemeOverlapDiagonalChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y X' Y' : Scheme.{u}}
variable (p : Y ⟶ X) (q : Y' ⟶ X') (a : X' ⟶ X) (b : Y' ⟶ Y)
variable (w : q ≫ a = b ≫ p) (M : Y.Modules)

/-- A refined diagonal law detects the pullback of the original diagonal equation. -/
lemma diagonal_pullback_of_refine
    (e : (pullback (Limits.pullback.fst p p)).obj M ≅
      (pullback (Limits.pullback.snd p p)).obj M)
    (he : DiagonalCompatible _ _ _ (Limits.pullback.diagonal_fst q)
      (Limits.pullback.diagonal_snd q) ((pullback b).obj M) (refine p q a b w e)) :
    (pullback b).map ((pullback (Limits.pullback.diagonal p)).map e.hom ≫
      (retractIso _ _ (Limits.pullback.diagonal_snd p) M).hom) =
        (pullback b).map (retractIso _ _ (Limits.pullback.diagonal_fst p) M).hom := by
  unfold DiagonalCompatible at he
  rw [← secondIso_diagonal p q a b w M, ← firstIso_diagonal p q a b w M] at he
  have hf := refine_hom p q a b w e
  dsimp only [Iso.app_hom] at hf
  rw [← Functor.map_comp_assoc, hf, Functor.map_comp, Category.assoc] at he
  have hn := (diagonalIso p q a b w).hom.naturality e.hom
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc ((pullback (Limits.pullback.diagonal q)).map
    ((pullback (overlapMap p q a b w)).map e.hom)), hn] at he
  simp only [Category.assoc] at he
  have hh := (cancel_epi ((pullback (Limits.pullback.diagonal q)).map
    ((firstIso p q a b w).hom.app M))).mp he
  have hh' := (cancel_epi ((diagonalIso p q a b w).hom.app
    ((pullback (Limits.pullback.fst p p)).obj M))).mp hh
  simpa only [Functor.map_comp] using hh'

end FLT.Mazur.SchemeOverlapRefinement
