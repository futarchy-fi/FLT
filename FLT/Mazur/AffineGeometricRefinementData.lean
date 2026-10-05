/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFiberProductRefinementCocycle
public import FLT.Mazur.AffineGeometricOverlapRefinementDiagonal
public import FLT.Mazur.AffineTripleOverlapRefinementSquares
public import FLT.Mazur.SchemeOverlapRefinementTripleCocycle

/-!
# Geometric descent data on affine refinements

The triple tensor refinement transports the original cocycle to the actual
restricted overlap. Together with its diagonal law, this constructs the
refined geometric descent datum from the supplied original datum.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricOverlapRefinement
open AffineGeometricDescent AffineGeometricOverlap AffineTripleOverlapMaps
open AffineTripleOverlapRefinement
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S R' S' : CommRingCat.{u}}
variable (φ : R ⟶ S) (ψ : R' ⟶ S') (a : R ⟶ R') (b : S ⟶ S')
variable (w : φ ≫ b = a ≫ ψ)
variable (M : (Spec S).Modules) (D : Data φ M)

/-- The actual refined categorical overlap satisfies its geometric cocycle. -/
theorem fiberProductOverlap_cocycle :
    let := ψ.hom.toAlgebra
    FiberProductCocycle R' S' ((pullback (Spec.map b)).obj M)
      (fiberProductOverlap φ ψ a b w M D) := by
  let := φ.hom.toAlgebra
  let := ψ.hom.toAlgebra
  have hw : b.hom.comp (algebraMap R S) = (algebraMap R' S').comp a.hom :=
    congrArg (fun f : R ⟶ S' ↦ f.hom) w
  exact refine_fiberProductCocycle a.hom b.hom hw M (toFiberProduct R S M D.val)
    (toFiberProduct_cocycle R S M D.val D.property.2)

/-- The actual refined tensor-chart overlap satisfies its geometric cocycle. -/
theorem overlap_cocycle :
    let := ψ.hom.toAlgebra
    AffineTripleOverlapPullback.CocycleCompatible R' S' ((pullback (Spec.map b)).obj M)
      (overlap φ ψ a b w M D) := by
  let := ψ.hom.toAlgebra
  exact (fromFiberProduct_cocycle_iff R' S' ((pullback (Spec.map b)).obj M) _).mpr
    (fiberProductOverlap_cocycle φ ψ a b w M D)

/-- Restrict an actual geometric descent datum along a commutative affine square. -/
def data : Data ψ ((pullback (Spec.map b)).obj M) :=
  ⟨overlap φ ψ a b w M D, overlap_diagonal φ ψ a b w M D,
    overlap_cocycle φ ψ a b w M D⟩

/-- The refined datum has precisely the previously constructed overlap. -/
theorem data_val : (data φ ψ a b w M D).val = overlap φ ψ a b w M D := rfl

end FLT.Mazur.AffineGeometricOverlapRefinement
