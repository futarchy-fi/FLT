/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeGeometricDescentCocycleTest

/-!
# Comparisons between unrelated covering charts

The product of two covering charts over the base maps to the actual double
overlap. The two maps into the cover need not agree: the descent isomorphism
supplies their comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeCrossCoverOverlap
open SchemeOverlapDiagonalChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y U V : Scheme.{u}} (p : Y ⟶ X) (b : U ⟶ Y) (c : V ⟶ Y)

/-- The product of the covering charts over the original base. -/
abbrev product := Limits.pullback (b ≫ p) (c ≫ p)

/-- The map from the cross-cover product to the original double overlap. -/
def pair : product p b c ⟶ Limits.pullback p p :=
  Limits.pullback.lift (Limits.pullback.fst (b ≫ p) (c ≫ p) ≫ b)
    (Limits.pullback.snd (b ≫ p) (c ≫ p) ≫ c) (by
      simpa only [Category.assoc] using Limits.pullback.condition (f := b ≫ p) (g := c ≫ p))

/-- The first projection of the cross-cover pair. -/
@[reassoc (attr := simp)]
theorem pair_fst : pair p b c ≫ Limits.pullback.fst p p =
    Limits.pullback.fst (b ≫ p) (c ≫ p) ≫ b := Limits.pullback.lift_fst _ _ _

/-- The second projection of the cross-cover pair. -/
@[reassoc (attr := simp)]
theorem pair_snd : pair p b c ≫ Limits.pullback.snd p p =
    Limits.pullback.snd (b ≫ p) (c ≫ p) ≫ c := Limits.pullback.lift_snd _ _ _

variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)

/-- Pullback of the original overlap with both projection paths normalized. -/
def transition :
    (pullback (Limits.pullback.fst (b ≫ p) (c ≫ p) ≫ b)).obj M ≅
      (pullback (Limits.pullback.snd (b ≫ p) (c ≫ p) ≫ c)).obj M :=
  normalize (Limits.pullback.fst p p) (Limits.pullback.snd p p) (pair p b c)
    _ _ (pair_fst p b c) (pair_snd p b c) M D.overlap

/-- The transition as a comparison of the two iterated covering-chart pullbacks. -/
def chartTransition :
    (pullback (Limits.pullback.fst (b ≫ p) (c ≫ p))).obj ((pullback b).obj M) ≅
      (pullback (Limits.pullback.snd (b ≫ p) (c ≫ p))).obj ((pullback c).obj M) :=
  (pullbackComp _ b).app M ≪≫ transition p b c D ≪≫ ((pullbackComp _ c).app M).symm

/-- Both projection identifications exhibit the transition as the given overlap pullback. -/
@[reassoc]
theorem transition_square :
    (SheafPullbackPathComparison.comparison (pair p b c) (Limits.pullback.fst p p)
        _ (pair_fst p b c)).hom.app M ≫ (transition p b c D).hom =
      (pullback (pair p b c)).map D.overlap.hom ≫
        (SheafPullbackPathComparison.comparison (pair p b c) (Limits.pullback.snd p p)
          _ (pair_snd p b c)).hom.app M := by
  simp only [transition, SchemeOverlapDiagonalChart.normalize, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv,
    Iso.app_hom, Functor.mapIso_hom, Iso.hom_inv_id_app_assoc]

end FLT.Mazur.SchemeCrossCoverOverlap
