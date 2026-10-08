/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePullbackCompositeTransport

/-!
# Normalization of affine pullback squares

Convert squares with a separate ring-composition chart and endpoint transport
into squares with a single objectwise comparison before specializing the sheaves.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineIteratedPullbackSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Replace both two-step sides of a commutative square by their composites. -/
theorem square_of_composite_eq {V : Type*} [Category V] {A B C D E F : V}
    (a : A ⟶ B) (l : A ⟶ C) (r : B ⟶ D) (l' : C ⟶ E) (r' : D ⟶ F)
    (b : E ⟶ F) (L : A ⟶ E) (R : B ⟶ F)
    (hl : l ≫ l' = L) (hr : r ≫ r' = R)
    (h : a ≫ r ≫ r' = l ≫ l' ≫ b) : a ≫ R = L ≫ b := by
  rw [← hl, ← hr, Category.assoc]
  exact h

variable {R S A B : CommRingCat.{u}}
variable (l : R ⟶ A) (r : S ⟶ A) (α : A ⟶ B) (l' : R ⟶ B) (r' : S ⟶ B)
variable (hl : l ≫ α = l') (hr : r ≫ α = r')
variable (M : (Spec R).Modules) (N : (Spec S).Modules)
variable (a : (pullback (Spec.map l)).obj M ⟶ (pullback (Spec.map r)).obj N)
variable (b : (pullback (Spec.map l')).obj M ⟶ (pullback (Spec.map r')).obj N)

/-- A transported affine square is an objectwise geometric pullback square. -/
theorem affine_square_normalized
    (h : (pullback (Spec.map α)).map a ≫
        (AffineRefinementPullback.compositionChart r α N).hom ≫
        (pullbackCongr (congrArg Spec.map hr)).hom.app N =
      (AffineRefinementPullback.compositionChart l α M).hom ≫
        (pullbackCongr (congrArg Spec.map hl)).hom.app M ≫ b) :
    (pullback (Spec.map α)).map a ≫
        (compositeIso (Spec.map α) (Spec.map r) (Spec.map r')
          ((Spec.map_comp r α).symm.trans (congrArg Spec.map hr)) N).hom =
      (compositeIso (Spec.map α) (Spec.map l) (Spec.map l')
          ((Spec.map_comp l α).symm.trans (congrArg Spec.map hl)) M).hom ≫ b :=
  square_of_composite_eq _ _ _ _ _ _ _ _
    (affineCompositionChart_trans l α l' hl M)
    (affineCompositionChart_trans r α r' hr N) h

end FLT.Mazur.AffineIteratedPullbackSections
