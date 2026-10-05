/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Restricting an actual overlap along a refinement square

A commutative square induces a map of categorical double overlaps. Pulling back
an overlap isomorphism along that map and conjugating by the projection charts
constructs the restricted overlap. The diagonal and cocycle laws are separate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeOverlapRefinement
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y X' Y' : Scheme.{u}}
variable (p : Y ⟶ X) (q : Y' ⟶ X') (a : X' ⟶ X) (b : Y' ⟶ Y)
variable (w : q ≫ a = b ≫ p)

/-- The canonical map from the refined double overlap to the original one. -/
def overlapMap : Limits.pullback q q ⟶ Limits.pullback p p :=
  Limits.pullback.lift (Limits.pullback.fst q q ≫ b) (Limits.pullback.snd q q ≫ b) (by
    rw [Category.assoc, ← w, ← Category.assoc, Limits.pullback.condition,
      Category.assoc, w, ← Category.assoc])

/-- The refinement map respects the first projection. -/
@[reassoc (attr := simp)]
theorem overlapMap_fst : overlapMap p q a b w ≫ Limits.pullback.fst p p =
    Limits.pullback.fst q q ≫ b := Limits.pullback.lift_fst _ _ _

/-- The refinement map respects the second projection. -/
@[reassoc (attr := simp)]
theorem overlapMap_snd : overlapMap p q a b w ≫ Limits.pullback.snd p p =
    Limits.pullback.snd q q ≫ b := Limits.pullback.lift_snd _ _ _

/-- The first-projection comparison for restriction of a sheaf. -/
def firstIso : pullback b ⋙ pullback (Limits.pullback.fst q q) ≅
    pullback (Limits.pullback.fst p p) ⋙ pullback (overlapMap p q a b w) :=
  pullbackComp _ _ ≪≫ pullbackCongr (overlapMap_fst p q a b w).symm ≪≫
    (pullbackComp _ _).symm

/-- The second-projection comparison for restriction of a sheaf. -/
def secondIso : pullback b ⋙ pullback (Limits.pullback.snd q q) ≅
    pullback (Limits.pullback.snd p p) ⋙ pullback (overlapMap p q a b w) :=
  pullbackComp _ _ ≪≫ pullbackCongr (overlapMap_snd p q a b w).symm ≪≫
    (pullbackComp _ _).symm

variable {M : Y.Modules}

/-- Pull back and normalize an overlap to the projection sheaves of the refinement. -/
def refine (e : (pullback (Limits.pullback.fst p p)).obj M ≅
    (pullback (Limits.pullback.snd p p)).obj M) :
    (pullback (Limits.pullback.fst q q)).obj ((pullback b).obj M) ≅
      (pullback (Limits.pullback.snd q q)).obj ((pullback b).obj M) :=
  (firstIso p q a b w).app M ≪≫ (pullback (overlapMap p q a b w)).mapIso e ≪≫
    ((secondIso p q a b w).app M).symm

/-- The restricted overlap satisfies its defining geometric conjugation square. -/
@[reassoc]
theorem refine_hom (e : (pullback (Limits.pullback.fst p p)).obj M ≅
    (pullback (Limits.pullback.snd p p)).obj M) :
    (refine p q a b w e).hom ≫ ((secondIso p q a b w).app M).hom =
      ((firstIso p q a b w).app M).hom ≫ (pullback (overlapMap p q a b w)).map e.hom := by
  simp [refine]

/-- Restriction preserves the compatibility square of overlap morphisms. -/
theorem refine_compatible {N : Y.Modules}
    (e : (pullback (Limits.pullback.fst p p)).obj M ≅
      (pullback (Limits.pullback.snd p p)).obj M)
    (e' : (pullback (Limits.pullback.fst p p)).obj N ≅
      (pullback (Limits.pullback.snd p p)).obj N) (f : M ⟶ N)
    (h : e.hom ≫ (pullback (Limits.pullback.snd p p)).map f =
      (pullback (Limits.pullback.fst p p)).map f ≫ e'.hom) :
    (refine p q a b w e).hom ≫
        (pullback (Limits.pullback.snd q q)).map ((pullback b).map f) =
      (pullback (Limits.pullback.fst q q)).map ((pullback b).map f) ≫
        (refine p q a b w e').hom := by
  have hl := (firstIso p q a b w).hom.naturality f
  have hr := (secondIso p q a b w).inv.naturality f
  dsimp only [Functor.comp_map] at hl hr
  have hc : (pullback (overlapMap p q a b w)).map e.hom ≫
      (pullback (overlapMap p q a b w)).map ((pullback (Limits.pullback.snd p p)).map f) =
    (pullback (overlapMap p q a b w)).map ((pullback (Limits.pullback.fst p p)).map f) ≫
      (pullback (overlapMap p q a b w)).map e'.hom := by
    rw [← Functor.map_comp, h, Functor.map_comp]
  dsimp only [refine, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv]
  simp only [Category.assoc]
  rw [← hr, ← Category.assoc ((pullback (overlapMap p q a b w)).map e.hom), hc,
    Category.assoc, ← Category.assoc ((firstIso p q a b w).hom.app M), ← hl,
    Category.assoc]

end FLT.Mazur.SchemeOverlapRefinement
