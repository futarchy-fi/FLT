/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeDescentAffineCharts

/-!
# Agreement of scheme and affine refinement data

Extracting tensor charts after geometric refinement gives exactly the existing
affine refinement construction. The categorical overlap round-trip supplies
the equality, including its diagonal and cocycle proofs by proof irrelevance.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent.Data
open AffineGeometricOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S R' S' : CommRingCat.{u}}
variable (φ : R ⟶ S) (ψ : R' ⟶ S') (a : R ⟶ R') (b : S ⟶ S')
variable (w : φ ≫ b = a ≫ ψ)
variable {M : (Spec S).Modules} (D : Data (Spec.map φ) M)

/-- The extracted datum has the specified normalized overlap. -/
theorem toAffine_val :
    let := φ.hom.toAlgebra
    (D.toAffine φ).val = fromFiberProduct R S M D.overlap := rfl

/-- Scheme refinement followed by extraction is the actual affine refinement datum. -/
theorem toAffine_refine :
    (D.refine (Spec.map φ) (Spec.map ψ) (Spec.map a) (Spec.map b)
      (AffineRefinementPullback.spec_square φ ψ a b w)).toAffine ψ =
    AffineGeometricOverlapRefinement.data φ ψ a b w M (D.toAffine φ) := by
  let := φ.hom.toAlgebra
  let := ψ.hom.toAlgebra
  apply Subtype.ext
  rw [toAffine_val, AffineGeometricOverlapRefinement.data_val]
  dsimp only [AffineGeometricOverlapRefinement.overlap,
    AffineGeometricOverlapRefinement.fiberProductOverlap]
  rw [refine_overlap, toAffine_overlap]

end FLT.Mazur.SchemeGeometricDescent.Data
