/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackCoordinateRecovery
public import FLT.Mazur.SchemeIndependentCanonicalOverlap

/-!
# Canonical base pullback through coordinate recovery

Canonical member comparisons recover the same base pullback comparison on
every coordinate. Two such recoveries intertwine canonical unequal overlaps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SheafPullbackCoordinateRecovery
open SheafPullbackPathComparison SchemeIndependentCanonicalOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y Y₁ Y₂ Z : Scheme.{u}}

/-- Recovering a canonical member pullback preserves the comparison to the base. -/
@[reassoc]
lemma recovery_comparison (p : Y ⟶ X) (i : Y₁ ⟶ Y) (f : Y₁ ⟶ X)
    (hi : i ≫ p = f) (l : Z ⟶ Y₁) (c : Z ⟶ Y) (hc : l ≫ i = c)
    (k : Z ⟶ X) (hl : l ≫ f = k) (hk : c ≫ p = k) (A : X.Modules) :
    (recovery l i c hc ((pullback p).obj A) ((comparison i p f hi).app A)).hom ≫
        (comparison l f k hl).hom.app A = (comparison c p k hk).hom.app A := by
  apply (cancel_epi ((comparison l i c hc).hom.app ((pullback p).obj A))).mp
  dsimp only [recovery, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  exact comparison_assoc l i p c f k hc hi hl hk A

/-- Canonical unequal overlaps commute with both canonical member recoveries. -/
lemma overlap_recovery (p : Y ⟶ X) (i : Y₁ ⟶ Y) (j : Y₂ ⟶ Y)
    (f : Y₁ ⟶ X) (g : Y₂ ⟶ X) (hi : i ≫ p = f) (hj : j ≫ p = g)
    (l : Z ⟶ Y₁) (r : Z ⟶ Y₂) (c : Z ⟶ Y) (d : Z ⟶ Y)
    (hc : l ≫ i = c) (hd : r ≫ j = d) (k : Z ⟶ X)
    (hl : l ≫ f = k) (hr : r ≫ g = k) (hk : c ≫ p = k) (hk' : d ≫ p = k)
    (A : X.Modules) :
    (overlap p p c d k hk hk' A).hom ≫
        (recovery r j d hd ((pullback p).obj A) ((comparison j p g hj).app A)).hom =
      (recovery l i c hc ((pullback p).obj A) ((comparison i p f hi).app A)).hom ≫
        (overlap f g l r k hl hr A).hom := by
  apply (cancel_mono ((comparison r g k hr).hom.app A)).mp
  dsimp only [overlap, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  rw [Category.assoc, recovery_comparison p j g hj r d hd k hr hk' A]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  exact (recovery_comparison p i f hi l c hc k hl hk A).symm

end FLT.Mazur.SheafPullbackCoordinateRecovery
