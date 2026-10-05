/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineRefinementPullback

/-!
# Restricting a map between reconstructions

A map that identifies two reconstructions still identifies them after any
commutative affine refinement square.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineRefinementPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S R' S' : CommRingCat.{u}}
variable (φ : R ⟶ S) (ψ : R' ⟶ S') (a : R ⟶ R') (b : S ⟶ S')
variable (w : φ ≫ b = a ≫ ψ)
variable {A B : (Spec R).Modules} {M : (Spec S).Modules}

/-- Pullback preserves a map identifying reconstruction charts with the same target. -/
@[reassoc]
theorem reconstruction_map (e : (pullback (Spec.map φ)).obj A ≅ M)
    (e' : (pullback (Spec.map φ)).obj B ≅ M) (f : A ⟶ B)
    (h : (pullback (Spec.map φ)).map f ≫ e'.hom = e.hom) :
    (pullback (Spec.map ψ)).map ((pullback (Spec.map a)).map f) ≫
        (reconstruction φ ψ a b w e').hom = (reconstruction φ ψ a b w e).hom := by
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using
    reconstruction_naturality φ ψ a b w e e' f (𝟙 M)
      (by simpa only [Category.comp_id] using h)

end FLT.Mazur.AffineRefinementPullback
