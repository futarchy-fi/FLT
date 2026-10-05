/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCanonicalOverlapChart
public import FLT.Mazur.AffineCanonicalOverlapRecognition
public import FLT.Mazur.AffineGeometricDescentMorphisms
public import FLT.Mazur.SchemeCanonicalMapRecognition

/-!
# Recognizing compatible maps from reconstruction squares

For coaction-compatible reconstruction charts, the geometric reconstruction
square implies compatibility with the actual descent data.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricDescentRecognition
open AffineGeometricDescent AffineGeometricOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] SchemePullbackOverlap.chartOverlap
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
variable {A B : (Spec R).Modules} [A.IsQuasicoherent] [B.IsQuasicoherent]
variable {M N : (Spec S).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
variable (D : Data φ M) (E : Data φ N)
variable (e : (pullback (Spec.map φ)).obj A ≅ M)
variable (e' : (pullback (Spec.map φ)).obj B ≅ N)

/-- A reconstruction square intertwines the actual geometric data on the cover. -/
theorem mapCompatible_of_reconstruction
    (he : CoactionCompatible φ A D e) (he' : CoactionCompatible φ B E e')
    (g : A ⟶ B) (f : M ⟶ N)
    (h : (pullback (Spec.map φ)).map g ≫ e'.hom = e.hom ≫ f) :
    MapCompatible φ D E f := by
  let := φ.hom.toAlgebra
  exact SchemePullbackOverlap.compatible_of_chartOverlap_eq (Spec.map φ)
    (Spec.map (CommRingCat.ofHom (AffineOverlapTensor.left R S)))
    (Spec.map (CommRingCat.ofHom (AffineOverlapTensor.right R S)))
    (canonicalTensorBase R S) (canonicalTensorBase_left R S)
    (canonicalTensorBase_right R S) e e' D.val E.val
    ((coactionCompatible_iff_canonical_overlap φ A D e
      (canonicalTensorBase R S) (canonicalTensorBase_left R S)
      (canonicalTensorBase_right R S)).mp he)
    ((coactionCompatible_iff_canonical_overlap φ B E e'
      (canonicalTensorBase R S) (canonicalTensorBase_left R S)
      (canonicalTensorBase_right R S)).mp he') g f h

end FLT.Mazur.AffineGeometricDescentRecognition
