/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineModulePullbackSections

/-!
# Pullback comparison for one affine refinement square

A commutative ring square identifies the two iterated sheaf pullbacks.
The comparison transports any reconstruction isomorphism, naturally in maps.
No cartesian or flatness hypothesis is needed for this comparison.
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

include w in
/-- The spectrum square commutes in the contravariant direction. -/
theorem spec_square : Spec.map ψ ≫ Spec.map a = Spec.map b ≫ Spec.map φ := by
  rw [← Spec.map_comp, ← Spec.map_comp, w]

/-- The two iterated pullbacks around the affine square are naturally isomorphic. -/
def squareIso :
    pullback (Spec.map a) ⋙ pullback (Spec.map ψ) ≅
      pullback (Spec.map φ) ⋙ pullback (Spec.map b) :=
  pullbackComp (Spec.map ψ) (Spec.map a) ≪≫
    pullbackCongr (spec_square φ ψ a b w) ≪≫
    (pullbackComp (Spec.map b) (Spec.map φ)).symm

variable {A B : (Spec R).Modules} {M N : (Spec S).Modules}

/-- Reconstruction survives restriction along the commutative square. -/
def reconstruction (e : (pullback (Spec.map φ)).obj A ≅ M) :
    (pullback (Spec.map ψ)).obj ((pullback (Spec.map a)).obj A) ≅
      (pullback (Spec.map b)).obj M :=
  (squareIso φ ψ a b w).app A ≪≫ (pullback (Spec.map b)).mapIso e

/-- Transported reconstruction respects every map satisfying the original square. -/
@[reassoc]
theorem reconstruction_naturality
    (e : (pullback (Spec.map φ)).obj A ≅ M)
    (e' : (pullback (Spec.map φ)).obj B ≅ N) (f : A ⟶ B) (g : M ⟶ N)
    (h : (pullback (Spec.map φ)).map f ≫ e'.hom = e.hom ≫ g) :
    (pullback (Spec.map ψ)).map ((pullback (Spec.map a)).map f) ≫
        (reconstruction φ ψ a b w e').hom =
      (reconstruction φ ψ a b w e).hom ≫ (pullback (Spec.map b)).map g := by
  have hn := (squareIso φ ψ a b w).hom.naturality f
  dsimp only [reconstruction, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  change _ ≫ (squareIso φ ψ a b w).hom.app B =
    (squareIso φ ψ a b w).hom.app A ≫ _ at hn
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, h,
    Functor.map_comp, Category.assoc]

end FLT.Mazur.AffineRefinementPullback
