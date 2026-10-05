/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFiberProductOverlap
public import FLT.Mazur.AffineGeometricDescent
public import FLT.Mazur.AffineRefinementPullback
public import FLT.Mazur.SchemeOverlapRefinement

/-!
# The actual geometric overlap on an affine refinement

Convert the supplied overlap to the categorical fiber product, restrict it along
the refinement square, and normalize it on the refined tensor-spectrum chart.
The categorical overlap is recovered exactly. Preservation of the diagonal and
cocycle equations must still be proved before this is a refined descent datum.
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

/-- Restrict the supplied overlap on the actual categorical fiber product. -/
def fiberProductOverlap :
    letI := ψ.hom.toAlgebra
    FiberProductOverlap R' S' ((pullback (Spec.map b)).obj M) := by
  letI := φ.hom.toAlgebra
  letI := ψ.hom.toAlgebra
  exact SchemeOverlapRefinement.refine (Spec.map φ) (Spec.map ψ) (Spec.map a) (Spec.map b)
    (AffineRefinementPullback.spec_square φ ψ a b w) (toFiberProduct R S M D.val)

/-- The specified overlap restricted to the refined tensor-spectrum chart. -/
def overlap :
    letI := ψ.hom.toAlgebra
    Overlap R' S' ((pullback (Spec.map b)).obj M) := by
  letI := ψ.hom.toAlgebra
  exact fromFiberProduct R' S' ((pullback (Spec.map b)).obj M)
    (fiberProductOverlap φ ψ a b w M D)

/-- Undoing normalization returns exactly the pulled-back categorical overlap. -/
theorem toFiberProduct_overlap :
    letI := ψ.hom.toAlgebra
    toFiberProduct R' S' ((pullback (Spec.map b)).obj M) (overlap φ ψ a b w M D) =
      fiberProductOverlap φ ψ a b w M D := by
  let _ := ψ.hom.toAlgebra
  exact toFiberProduct_fromFiberProduct R' S' ((pullback (Spec.map b)).obj M) _

end FLT.Mazur.AffineGeometricOverlapRefinement
