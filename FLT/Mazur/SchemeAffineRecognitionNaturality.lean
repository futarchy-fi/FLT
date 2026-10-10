/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineReconstructionRecognition

/-!
# Naturality of the actual affine recognition comparison

A commutative candidate reconstruction square restricts to every affine chart.
The proof uses the naturality of the pullback-square comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent.Data
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} (p : Y ⟶ X)
variable {A B : X.Modules} {M N : Y.Modules}
variable (e : (pullback p).obj A ≅ M) (e' : (pullback p).obj B ≅ N)
variable (f : A ⟶ B) (g : M ⟶ N)
variable (h : (pullback p).map f ≫ e'.hom = e.hom ≫ g)
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
variable (a : Spec R ⟶ X) (b : Spec S ⟶ Y) (w : Spec.map φ ≫ a = b ≫ p)

include h in
/-- Candidate reconstruction naturality persists on each actual affine chart. -/
@[reassoc]
lemma recognitionChart_naturality :
    (pullback (Spec.map φ)).map ((pullback a).map f) ≫
        (recognitionChart p B e' φ a b w).hom =
      (recognitionChart p A e φ a b w).hom ≫ (pullback b).map g := by
  have hn := (SchemePullbackSquare.squareIso p (Spec.map φ) a b w).hom.naturality f
  dsimp only [Functor.comp_map] at hn
  simp only [recognitionChart, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, h,
    Functor.map_comp, Category.assoc]

end FLT.Mazur.SchemeGeometricDescent.Data
