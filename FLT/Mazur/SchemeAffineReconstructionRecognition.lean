/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineChartDescent
public import FLT.Mazur.SchemeCanonicalOverlapRefinement
public import FLT.Mazur.AffineCanonicalOverlapChart
public import FLT.Mazur.AffineCanonicalOverlapRecognition

/-!
# Recognition of affine charts from a global reconstruction

An original-overlap equality restricts to the canonical overlap of the actual
affine chart reconstruction. The coefficient coaction criterion then applies.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent.Data
open SchemePullbackOverlap AffineGeometricOverlap AffineGeometricDescentRecognition
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} (p : Y ⟶ X) {M : Y.Modules} (D : Data p M)
variable (A : X.Modules) (e : (pullback p).obj A ≅ M)
variable (he : D.overlap = chartOverlap p (Limits.pullback.fst p p)
  (Limits.pullback.snd p p) (Limits.pullback.fst p p ≫ p)
  rfl Limits.pullback.condition.symm A e)
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
variable (a : Spec R ⟶ X) (b : Spec S ⟶ Y) (w : Spec.map φ ≫ a = b ≫ p)

/-- The candidate reconstruction restricted to an affine chart square. -/
def recognitionChart :
    (pullback (Spec.map φ)).obj ((pullback a).obj A) ≅ (pullback b).obj M :=
  (SchemePullbackSquare.squareIso p (Spec.map φ) a b w).app A ≪≫ (pullback b).mapIso e

include he in
/-- The extracted affine datum has the canonical overlap of the restricted reconstruction. -/
lemma affineChart_canonical_overlap :
    let := φ.hom.toAlgebra
    (D.affineChart φ p a b w).val = chartOverlap (Spec.map φ)
      (Spec.map (CommRingCat.ofHom (AffineOverlapTensor.left R S)))
      (Spec.map (CommRingCat.ofHom (AffineOverlapTensor.right R S)))
      (canonicalTensorBase R S) (canonicalTensorBase_left R S)
      (canonicalTensorBase_right R S) ((pullback a).obj A)
      (recognitionChart p A e φ a b w) := by
  let := φ.hom.toAlgebra
  change fromFiberProduct R S ((pullback b).obj M)
    (SchemeOverlapRefinement.refine p (Spec.map φ) a b w D.overlap) = _
  rw [he, SchemeOverlapRefinement.refine_chartOverlap p (Spec.map φ) a b w
    _ rfl Limits.pullback.condition.symm (canonicalFiberBase R S)
    rfl Limits.pullback.condition.symm A e]
  exact fromFiberProduct_chartOverlap R S ((pullback a).obj A) _

variable [((pullback a).obj A).IsQuasicoherent] [((pullback b).obj M).IsQuasicoherent]

include he in
/-- The global overlap equation proves coefficient coaction compatibility on every chart. -/
lemma affineChart_coactionCompatible :
    CoactionCompatible φ ((pullback a).obj A) (D.affineChart φ p a b w)
      (recognitionChart p A e φ a b w) := by
  let := φ.hom.toAlgebra
  exact (coactionCompatible_iff_canonical_overlap φ ((pullback a).obj A)
    (D.affineChart φ p a b w) (recognitionChart p A e φ a b w)
    (canonicalTensorBase R S) (canonicalTensorBase_left R S)
    (canonicalTensorBase_right R S)).mpr (D.affineChart_canonical_overlap p A e he φ a b w)

end FLT.Mazur.SchemeGeometricDescent.Data
