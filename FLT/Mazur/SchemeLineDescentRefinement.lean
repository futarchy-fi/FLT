/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeLineCanonicalFunctor
public import FLT.Mazur.SchemeCanonicalOverlapRefinement
public import FLT.Mazur.SchemeCanonicalRecoveryCompatibility

/-!
# Pullback of line descent data along a commutative square

Refinement pulls back the original sheaf and overlap. Its comparison with
canonical descent uses the actual sheaf pullback isomorphism around the square.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent
open SchemePicard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y X' Y' : Scheme.{u}}
variable (p : Y ⟶ X) (q : Y' ⟶ X') (a : X' ⟶ X) (b : Y' ⟶ Y)
variable (w : q ≫ a = b ≫ p)

/-- Refine line descent data by pulling back its sheaf and its original overlap. -/
def lineRefine : LineData p ⥤ LineData q where
  obj D := ⟨(pullback b).obj D.obj, D.rankOne.pullback b, D.datum.refine p q a b w⟩
  map f := ⟨(pullback b).map f.val,
    Data.refine_mapCompatible p _ q a b w _ f.val f.property⟩
  map_id D := Subtype.ext ((pullback b).map_id D.obj)
  map_comp f g := Subtype.ext ((pullback b).map_comp f.val g.val)

/-- The square comparison respects the original refined canonical overlap. -/
lemma canonical_square_compatible (A : X.Modules) :
    (canonical q ((pullback a).obj A)).MapCompatible q
      ((canonical p A).refine p q a b w)
      ((SchemePullbackSquare.squareIso p q a b w).hom.app A) := by
  apply canonical_recovery_compatible q _ _ ((SchemePullbackSquare.squareIso p q a b w).app A)
  have h := SchemeOverlapRefinement.refine_chartOverlap p q a b w
    (Limits.pullback.fst p p ≫ p) rfl Limits.pullback.condition.symm
    (Limits.pullback.fst q q ≫ q) rfl Limits.pullback.condition.symm A (Iso.refl _)
  simpa only [Data.refine, canonical, SchemePullbackOverlap.chartOverlap,
    Functor.mapIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl,
    Functor.comp_obj] using h

/-- Canonical descent commutes naturally with refinement along the actual square. -/
def lineCanonicalRefine :
    lineBundlePullback a ⋙ lineCanonical q ≅ lineCanonical p ⋙ lineRefine p q a b w :=
  NatIso.ofComponents (fun A ↦ LineData.isoMk q
    ((SchemePullbackSquare.squareIso p q a b w).app A.val)
    (canonical_square_compatible p q a b w A.val)) (fun {A B} f ↦ by
      apply LineData.hom_ext
      exact (SchemePullbackSquare.squareIso p q a b w).hom.naturality f.hom)

end FLT.Mazur.SchemeGeometricDescent
