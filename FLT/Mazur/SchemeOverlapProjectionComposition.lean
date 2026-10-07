/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOverlapRefinementCoherence
public import FLT.Mazur.SchemePullbackCompositeCharts

/-!
# Composition of the projection comparisons on scheme overlaps

The actual first and second projection charts commute with successive
refinement. The overlap composition chart includes the equality of the
categorical double-overlap maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeOverlapRefinement
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y X' Y' X'' Y'' : Scheme.{u}}
variable (p : Y ⟶ X) (q : Y' ⟶ X') (a : X' ⟶ X) (b : Y' ⟶ Y)
variable (w : q ≫ a = b ≫ p)
variable (r : Y'' ⟶ X'') (c : X'' ⟶ X') (d : Y'' ⟶ Y')
variable (v : r ≫ c = d ≫ q)

/-- The comparison for successive pullbacks between actual double overlaps. -/
def overlapCompositionIso :
    pullback (overlapMap p q a b w) ⋙ pullback (overlapMap q r c d v) ≅
      pullback (overlapMap p r (c ≫ a) (d ≫ b) (square_comp p q a b w r c d v)) :=
  comparison _ _ _ (overlapMap_comp p q a b w r c d v)

/-- First projection charts respect composition of refinement squares. -/
@[reassoc]
theorem firstIso_composition (M : Y.Modules) :
    (pullback (Limits.pullback.fst r r)).map ((pullbackComp d b).hom.app M) ≫
        (firstIso p r (c ≫ a) (d ≫ b) (square_comp p q a b w r c d v)).hom.app M =
      (firstIso q r c d v).hom.app ((pullback b).obj M) ≫
        (pullback (overlapMap q r c d v)).map ((firstIso p q a b w).hom.app M) ≫
        (overlapCompositionIso p q a b w r c d v).hom.app
          ((pullback (Limits.pullback.fst p p)).obj M) := by
  simpa only [firstIso, overlapCompositionIso, SchemePullbackSquare.squareIso,
    comparison, pullbackCongr, eqToIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, eqToHom_refl, NatTrans.id_app,
    Category.comp_id] using
    SchemePullbackSquare.squareIso_composite_charts
      (Limits.pullback.fst p p) (Limits.pullback.fst q q) (Limits.pullback.fst r r)
      b (overlapMap p q a b w) d (overlapMap q r c d v)
      (overlapMap_fst p q a b w).symm (overlapMap_fst q r c d v).symm
      (d ≫ b) (overlapMap p r (c ≫ a) (d ≫ b) (square_comp p q a b w r c d v))
      rfl (overlapMap_comp p q a b w r c d v)
      (overlapMap_fst p r (c ≫ a) (d ≫ b) (square_comp p q a b w r c d v)).symm M

/-- Second projection charts respect composition of refinement squares. -/
@[reassoc]
theorem secondIso_composition (M : Y.Modules) :
    (pullback (Limits.pullback.snd r r)).map ((pullbackComp d b).hom.app M) ≫
        (secondIso p r (c ≫ a) (d ≫ b) (square_comp p q a b w r c d v)).hom.app M =
      (secondIso q r c d v).hom.app ((pullback b).obj M) ≫
        (pullback (overlapMap q r c d v)).map ((secondIso p q a b w).hom.app M) ≫
        (overlapCompositionIso p q a b w r c d v).hom.app
          ((pullback (Limits.pullback.snd p p)).obj M) := by
  simpa only [secondIso, overlapCompositionIso, SchemePullbackSquare.squareIso,
    comparison, pullbackCongr, eqToIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, eqToHom_refl, NatTrans.id_app,
    Category.comp_id] using
    SchemePullbackSquare.squareIso_composite_charts
      (Limits.pullback.snd p p) (Limits.pullback.snd q q) (Limits.pullback.snd r r)
      b (overlapMap p q a b w) d (overlapMap q r c d v)
      (overlapMap_snd p q a b w).symm (overlapMap_snd q r c d v).symm
      (d ≫ b) (overlapMap p r (c ≫ a) (d ≫ b) (square_comp p q a b w r c d v))
      rfl (overlapMap_comp p q a b w r c d v)
      (overlapMap_snd p r (c ≫ a) (d ≫ b) (square_comp p q a b w r c d v)).symm M

end FLT.Mazur.SchemeOverlapRefinement
