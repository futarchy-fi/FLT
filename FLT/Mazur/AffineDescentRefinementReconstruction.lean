/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineGeometricDescentMorphisms
public import FLT.Mazur.AffineQuasicoherentPullbackFaithful
public import FLT.Mazur.AffineRefinementPullback

/-!
# Affine refinement of descended sheaves and reconstruction maps

Restrict a descended sheaf along one affine refinement square. Its pullback
reconstructs the restricted input sheaf, and restricted descended maps satisfy
the reconstruction square. Faithful flatness of the refined cover makes that
square determine the restricted map uniquely.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineDescentRefinement
open AffineGeometricDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S R' S' : CommRingCat.{u}}
variable (φ : R ⟶ S) (ψ : R' ⟶ S') (a : R ⟶ R') (b : S ⟶ S')
variable (w : φ ≫ b = a ≫ ψ) (hφ : φ.hom.FaithfullyFlat)
variable {M N : (Spec S).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
variable (D : Data φ M) (E : Data φ N)

/-- Restrict the effectively descended sheaf along the base refinement. -/
abbrev sheaf : (Spec R').Modules :=
  (pullback (Spec.map a)).obj (descendedSheaf φ M D hφ)

instance : (sheaf φ a hφ D).IsQuasicoherent :=
  AffineModulePullbackSections.isQuasicoherent_pullback a _

/-- The restricted descended sheaf reconstructs the restricted original sheaf. -/
def reconstruction :
    (pullback (Spec.map ψ)).obj (sheaf φ a hφ D) ≅
      (pullback (Spec.map b)).obj M :=
  AffineRefinementPullback.reconstruction φ ψ a b w
    (AffineGeometricDescent.reconstruction φ M D hφ)

variable (f : M ⟶ N) (hf : MapCompatible φ D E f)

/-- The restricted descended morphism. -/
abbrev map : sheaf φ a hφ D ⟶ sheaf φ a hφ E :=
  (pullback (Spec.map a)).map (descendedMap φ D E f hf hφ)

/-- Restriction of a descended map satisfies the actual refined reconstruction square. -/
@[reassoc]
theorem reconstruction_naturality :
    (pullback (Spec.map ψ)).map (map φ a hφ D E f hf) ≫
        (reconstruction φ ψ a b w hφ E).hom =
      (reconstruction φ ψ a b w hφ D).hom ≫ (pullback (Spec.map b)).map f :=
  AffineRefinementPullback.reconstruction_naturality φ ψ a b w
    (AffineGeometricDescent.reconstruction φ M D hφ)
    (AffineGeometricDescent.reconstruction φ N E hφ)
    (descendedMap φ D E f hf hφ) f
    (AffineGeometricDescent.reconstruction_naturality φ D E f hf hφ)

/-- The refined reconstruction square uniquely determines the restricted map. -/
theorem map_unique (hψ : ψ.hom.FaithfullyFlat)
    (g : sheaf φ a hφ D ⟶ sheaf φ a hφ E)
    (hg : (pullback (Spec.map ψ)).map g ≫ (reconstruction φ ψ a b w hφ E).hom =
      (reconstruction φ ψ a b w hφ D).hom ≫ (pullback (Spec.map b)).map f) :
    g = map φ a hφ D E f hf :=
  AffineQuasicoherentPullbackFaithful.reconstruction_unique ψ hψ
    (reconstruction φ ψ a b w hφ E) g _
    (hg.trans (reconstruction_naturality φ ψ a b w hφ D E f hf).symm)

end FLT.Mazur.AffineDescentRefinement
