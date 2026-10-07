/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineNamedRefinementReconstruction

/-!
# Naturality of named affine reconstruction charts

A map satisfying the original reconstruction square satisfies the refined
square with the specified cover endpoint.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineNamedRefinementReconstruction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] chart AffineRefinementPullback.reconstruction
variable {R S R' S' : CommRingCat.{u}} {Y : Scheme.{u}}
variable (φ : R ⟶ S) (ψ : R' ⟶ S') (a : R ⟶ R') (b : S ⟶ S')
variable (w : φ ≫ b = a ≫ ψ) (t : Spec S ⟶ Y) (t' : Spec S' ⟶ Y)
variable (ht : Spec.map b ≫ t = t')
variable {A B : (Spec R).Modules} {M : Y.Modules}

/-- A reconstruction-preserving map remains so after named affine refinement. -/
theorem chart_naturality
    (e : (pullback (Spec.map φ)).obj A ≅ (pullback t).obj M)
    (e' : (pullback (Spec.map φ)).obj B ≅ (pullback t).obj M) (f : A ⟶ B)
    (hf : (pullback (Spec.map φ)).map f ≫ e'.hom = e.hom) :
    (pullback (Spec.map ψ)).map ((pullback (Spec.map a)).map f) ≫
        (chart φ ψ a b w t t' ht e').hom = (chart φ ψ a b w t t' ht e).hom := by
  have h := AffineRefinementPullback.reconstruction_naturality φ ψ a b w
    e e' f (𝟙 _) (by simpa only [Category.comp_id] using hf)
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at h
  rw [chart_hom φ ψ a b w t t' ht e', chart_hom φ ψ a b w t t' ht e,
    ← Category.assoc, h]

end FLT.Mazur.AffineNamedRefinementReconstruction
