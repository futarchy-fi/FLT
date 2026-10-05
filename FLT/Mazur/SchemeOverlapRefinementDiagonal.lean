/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOverlapDiagonalChart
public import FLT.Mazur.SchemeOverlapRefinementCoherence
public import FLT.Mazur.SheafPullbackRetractionSquare

/-!
# Diagonal preservation for geometric overlap refinement

Restricting an overlap along a commutative square preserves its actual sheaf
diagonal equation. Both projection comparisons commute with the diagonal.
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
variable (w : q ≫ a = b ≫ p)

/-- Compare the two routes from the refined diagonal to the original double overlap. -/
def diagonalIso :
    pullback (overlapMap p q a b w) ⋙ pullback (Limits.pullback.diagonal q) ≅
      pullback (Limits.pullback.diagonal p) ⋙ pullback b :=
  pullbackComp _ _ ≪≫ pullbackCongr (diagonal_overlapMap p q a b w) ≪≫
    (pullbackComp _ _).symm

/-- The first projection comparison agrees with restriction to the diagonal. -/
@[reassoc]
theorem firstIso_diagonal (M : Y.Modules) :
    (pullback (Limits.pullback.diagonal q)).map ((firstIso p q a b w).hom.app M) ≫
      (diagonalIso p q a b w).hom.app ((pullback (Limits.pullback.fst p p)).obj M) ≫
      (pullback b).map (retractIso _ _ (Limits.pullback.diagonal_fst p) M).hom =
    (retractIso _ _ (Limits.pullback.diagonal_fst q) ((pullback b).obj M)).hom := by
  simpa only [firstIso, diagonalIso, SheafPullbackPathComparison.comparison,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv,
    NatTrans.comp_app, Category.assoc, pullbackCongr, eqToIso] using
    SheafPullbackRetractionSquare.square_retract
      (Limits.pullback.fst p p) (Limits.pullback.fst q q) b (overlapMap p q a b w)
      (overlapMap_fst p q a b w) (Limits.pullback.diagonal p) (Limits.pullback.diagonal q)
      (diagonal_overlapMap p q a b w) (Limits.pullback.diagonal_fst p)
      (Limits.pullback.diagonal_fst q) M

/-- The second projection comparison agrees with restriction to the diagonal. -/
@[reassoc]
theorem secondIso_diagonal (M : Y.Modules) :
    (pullback (Limits.pullback.diagonal q)).map ((secondIso p q a b w).hom.app M) ≫
      (diagonalIso p q a b w).hom.app ((pullback (Limits.pullback.snd p p)).obj M) ≫
      (pullback b).map (retractIso _ _ (Limits.pullback.diagonal_snd p) M).hom =
    (retractIso _ _ (Limits.pullback.diagonal_snd q) ((pullback b).obj M)).hom := by
  simpa only [secondIso, diagonalIso, SheafPullbackPathComparison.comparison,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv,
    NatTrans.comp_app, Category.assoc, pullbackCongr, eqToIso] using
    SheafPullbackRetractionSquare.square_retract
      (Limits.pullback.snd p p) (Limits.pullback.snd q q) b (overlapMap p q a b w)
      (overlapMap_snd p q a b w) (Limits.pullback.diagonal p) (Limits.pullback.diagonal q)
      (diagonal_overlapMap p q a b w) (Limits.pullback.diagonal_snd p)
      (Limits.pullback.diagonal_snd q) M

/-- An actual diagonal identity is preserved by overlap refinement. -/
theorem refine_diagonal (M : Y.Modules)
    (e : (pullback (Limits.pullback.fst p p)).obj M ≅
      (pullback (Limits.pullback.snd p p)).obj M)
    (he : DiagonalCompatible _ _ _ (Limits.pullback.diagonal_fst p)
      (Limits.pullback.diagonal_snd p) M e) :
    DiagonalCompatible _ _ _ (Limits.pullback.diagonal_fst q)
      (Limits.pullback.diagonal_snd q) ((pullback b).obj M) (refine p q a b w e) := by
  unfold DiagonalCompatible at he ⊢
  dsimp only [refine, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [← secondIso_diagonal p q a b w M]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [Functor.map_comp, Functor.comp_obj,
    Category.comp_id, Category.assoc]
  have hn := (diagonalIso p q a b w).hom.naturality e.hom
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc ((pullback (Limits.pullback.diagonal q)).map
    ((pullback (overlapMap p q a b w)).map e.hom)), hn]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [he]
  exact firstIso_diagonal p q a b w M

end FLT.Mazur.SchemeOverlapRefinement
