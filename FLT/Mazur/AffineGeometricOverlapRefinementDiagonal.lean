/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFiberProductDiagonal
public import FLT.Mazur.AffineGeometricOverlapRefinement
public import FLT.Mazur.SchemeOverlapRefinementDiagonal

/-!
# The diagonal law for the refined affine overlap

The constructed refinement of an affine geometric descent datum satisfies
the actual sheaf diagonal equation. The cocycle remains a separate condition.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricOverlapRefinement
open AffineGeometricDescent AffineGeometricOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S R' S' : CommRingCat.{u}}
variable (φ : R ⟶ S) (ψ : R' ⟶ S') (a : R ⟶ R') (b : S ⟶ S')
variable (w : φ ≫ b = a ≫ ψ)
variable (M : (Spec S).Modules) (D : Data φ M)

/-- The refined categorical overlap has the geometric diagonal identity. -/
theorem fiberProductOverlap_diagonal :
    letI := ψ.hom.toAlgebra
    FiberProductDiagonal R' S' ((pullback (Spec.map b)).obj M)
      (fiberProductOverlap φ ψ a b w M D) := by
  let := φ.hom.toAlgebra
  let := ψ.hom.toAlgebra
  exact SchemeOverlapRefinement.refine_diagonal (Spec.map φ) (Spec.map ψ)
    (Spec.map a) (Spec.map b) (AffineRefinementPullback.spec_square φ ψ a b w) M
    (toFiberProduct R S M D.val) (toFiberProduct_diagonal R S M D.val D.property.1)

/-- The specified refined affine overlap satisfies its actual sheaf diagonal equation. -/
theorem overlap_diagonal :
    letI := ψ.hom.toAlgebra
    AffineOverlapDiagonal.DiagonalCompatible R' S' ((pullback (Spec.map b)).obj M)
      (overlap φ ψ a b w M D) := by
  let := ψ.hom.toAlgebra
  exact (fromFiberProduct_diagonal_iff R' S' ((pullback (Spec.map b)).obj M) _).mpr
    (fiberProductOverlap_diagonal φ ψ a b w M D)

end FLT.Mazur.AffineGeometricOverlapRefinement
