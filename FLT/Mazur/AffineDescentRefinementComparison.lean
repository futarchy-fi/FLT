/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineDescentRefinementReconstruction
public import FLT.Mazur.AffineGeometricDescentRecognition

/-!
# Comparison with descent on an affine refinement

The restricted descended sheaf is identified with a separately descended refined
datum once the reconstruction chart is proved compatible with that datum's
coaction. Reconstruction uniqueness supplies naturality of these comparisons.
The compatibility hypotheses remain explicit; constructing refined geometric
data and verifying these hypotheses are separate obligations.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.AffineGeometricDescentRecognition
open AffineGeometricDescent
variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : φ.hom.FaithfullyFlat)
variable {A B : (Spec R).Modules} [A.IsQuasicoherent] [B.IsQuasicoherent]
variable {M N : (Spec S).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
variable (D : Data φ M) (E : Data φ N)
variable (e : (pullback (Spec.map φ)).obj A ≅ M)
variable (e' : (pullback (Spec.map φ)).obj B ≅ N)
variable (he : CoactionCompatible φ A D e) (he' : CoactionCompatible φ B E e')

/-- Recognition is natural for maps satisfying the original reconstruction square. -/
@[reassoc]
theorem sheafIso_naturality (f : M ⟶ N) (hf : MapCompatible φ D E f) (g : A ⟶ B)
    (hg : (pullback (Spec.map φ)).map g ≫ e'.hom = e.hom ≫ f) :
    (sheafIso φ hφ A D e he).hom ≫ descendedMap φ D E f hf hφ =
      g ≫ (sheafIso φ hφ B E e' he').hom := by
  apply AffineQuasicoherentPullbackFaithful.reconstruction_unique φ hφ
    (reconstruction φ N E hφ)
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, reconstruction_naturality,
    ← Category.assoc, sheafIso_reconstruction, Category.assoc, sheafIso_reconstruction]
  exact hg.symm

end FLT.Mazur.AffineGeometricDescentRecognition

namespace FLT.Mazur.AffineDescentRefinement
open AffineGeometricDescent AffineGeometricDescentRecognition
variable {R S R' S' : CommRingCat.{u}}
variable (φ : R ⟶ S) (ψ : R' ⟶ S') (a : R ⟶ R') (b : S ⟶ S')
variable (w : φ ≫ b = a ≫ ψ) (hφ : φ.hom.FaithfullyFlat) (hψ : ψ.hom.FaithfullyFlat)
variable {M N : (Spec S).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
local instance (P : (Spec S).Modules) [P.IsQuasicoherent] :
    ((pullback (Spec.map b)).obj P).IsQuasicoherent :=
  AffineModulePullbackSections.isQuasicoherent_pullback b P
variable (D : Data φ M) (D' : Data ψ ((pullback (Spec.map b)).obj M))
variable (he : CoactionCompatible ψ (sheaf φ a hφ D) D'
  (reconstruction φ ψ a b w hφ D))

/-- Coaction compatibility identifies restriction with descent of the refined datum. -/
def comparisonIso :
    sheaf φ a hφ D ≅ descendedSheaf ψ ((pullback (Spec.map b)).obj M) D' hψ :=
  sheafIso ψ hψ (sheaf φ a hφ D) D' (reconstruction φ ψ a b w hφ D) he

/-- The comparison has the specified refined geometric reconstruction. -/
@[reassoc]
theorem comparisonIso_reconstruction :
    (pullback (Spec.map ψ)).map (comparisonIso φ ψ a b w hφ hψ D D' he).hom ≫
        (AffineGeometricDescent.reconstruction ψ ((pullback (Spec.map b)).obj M) D' hψ).hom =
      (reconstruction φ ψ a b w hφ D).hom :=
  sheafIso_reconstruction ψ hψ (sheaf φ a hφ D) D' _ he

/-- Refinement comparison is natural for compatible original and refined maps. -/
@[reassoc]
theorem comparisonIso_naturality
    (E : Data φ N) (E' : Data ψ ((pullback (Spec.map b)).obj N))
    (he' : CoactionCompatible ψ (sheaf φ a hφ E) E' (reconstruction φ ψ a b w hφ E))
    (f : M ⟶ N) (hf : MapCompatible φ D E f)
    (hf' : MapCompatible ψ D' E' ((pullback (Spec.map b)).map f)) :
    (comparisonIso φ ψ a b w hφ hψ D D' he).hom ≫
        descendedMap ψ D' E' ((pullback (Spec.map b)).map f) hf' hψ =
      map φ a hφ D E f hf ≫ (comparisonIso φ ψ a b w hφ hψ E E' he').hom :=
  sheafIso_naturality ψ hψ D' E' _ _ he he' _ hf' _
    (reconstruction_naturality φ ψ a b w hφ D E f hf)

end FLT.Mazur.AffineDescentRefinement
