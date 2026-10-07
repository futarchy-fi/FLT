/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeGeometricDescentCocycleTest
public import FLT.Mazur.AffineGeometricRefinementData
public import FLT.Mazur.AffineFiberProductCocycleChart

/-!
# Extracting affine charts from actual scheme descent data

The categorical diagonal and triple-overlap equations imply the tensor-chart
laws required by effective affine descent. A commutative affine chart square
therefore produces an actual affine descent datum, without new compatibility
hypotheses.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent.Data
open AffineGeometricOverlap AffineTripleOverlapMaps
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
variable {M : (Spec S).Modules} (D : Data (Spec.map φ) M)

/-- The canonical scheme cocycle holds on the actual affine tensor triple chart. -/
theorem affine_cocycle :
    let := φ.hom.toAlgebra
    FiberProductCocycle R S M D.overlap := by
  let := φ.hom.toAlgebra
  apply (fiberProductCocycle_iff_scheme R S M D.overlap).mpr
  exact D.cocycle_on_pairs (Spec.map φ)
    (fiberProductPair R S (pair12 R S)) (fiberProductPair R S (pair23 R S))
    (fiberProductPair R S (pair13 R S))
    (Spec.map (CommRingCat.ofHom (coord1 R S)))
    (Spec.map (CommRingCat.ofHom (coord2 R S)))
    (Spec.map (CommRingCat.ofHom (coord3 R S)))
    (fiberProductPair_fst R S (pair12 R S) (coord1 R S) (pair12_left R S))
    (fiberProductPair_snd R S (pair12 R S) (coord2 R S) (pair12_right R S))
    (fiberProductPair_fst R S (pair23 R S) (coord2 R S) (pair23_left R S))
    (fiberProductPair_snd R S (pair23 R S) (coord3 R S) (pair23_right R S))
    (fiberProductPair_fst R S (pair13 R S) (coord1 R S) (pair13_left R S))
    (fiberProductPair_snd R S (pair13 R S) (coord3 R S) (pair13_right R S))

/-- Convert a scheme datum on spectra to its actual tensor-chart descent datum. -/
def toAffine : AffineGeometricDescent.Data φ M := by
  let := φ.hom.toAlgebra
  exact ⟨fromFiberProduct R S M D.overlap,
    (fromFiberProduct_diagonal_iff R S M D.overlap).mpr D.diagonal,
    (fromFiberProduct_cocycle_iff R S M D.overlap).mpr (D.affine_cocycle φ)⟩

/-- The affine datum recovers the exact categorical overlap that was supplied. -/
theorem toAffine_overlap :
    let := φ.hom.toAlgebra
    toFiberProduct R S M (D.toAffine φ).val = D.overlap := by
  let := φ.hom.toAlgebra
  exact toFiberProduct_fromFiberProduct R S M D.overlap

variable {X Y : Scheme.{u}} (p : Y ⟶ X) {N : Y.Modules} (E : Data p N)
variable (a : Spec R ⟶ X) (b : Spec S ⟶ Y) (w : Spec.map φ ≫ a = b ≫ p)

/-- Extract the actual affine datum along an affine chart square of a scheme cover. -/
def affineChart : AffineGeometricDescent.Data φ ((pullback b).obj N) :=
  (E.refine p (Spec.map φ) a b w).toAffine φ

/-- The extracted affine chart reconstructs the actual restriction of the scheme overlap. -/
theorem affineChart_overlap :
    let := φ.hom.toAlgebra
    toFiberProduct R S ((pullback b).obj N) (E.affineChart φ p a b w).val =
      SchemeOverlapRefinement.refine p (Spec.map φ) a b w E.overlap :=
  (E.refine p (Spec.map φ) a b w).toAffine_overlap φ

end FLT.Mazur.SchemeGeometricDescent.Data
