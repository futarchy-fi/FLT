/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFiberProductOverlap
public import FLT.Mazur.AffineOverlapDiagonal
public import FLT.Mazur.SchemeOverlapDiagonalDetection

/-!
# The diagonal law on categorical and affine overlaps

The tensor-spectrum chart preserves and detects the actual sheaf diagonal
identity. Consequently an affine overlap satisfying the diagonal law gives
a categorical fiber-product overlap satisfying the same law.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricOverlap
open AffineOverlapTensor AffineOverlapPullback AffineOverlapDiagonal
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The inverse tensor chart takes the multiplication morphism to the categorical diagonal. -/
theorem diagonal_chart_inv :
    Spec.map (CommRingCat.ofHom (diagonalRing R S)) ≫ (pullbackSpecIso R S S).inv =
      Limits.pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  rw [← diagonal_chart R S, Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable (M : (Spec (.of S)).Modules)

/-- The diagonal identity for an overlap on the categorical fiber product. -/
abbrev FiberProductDiagonal (e : FiberProductOverlap R S M) : Prop :=
  let p := Spec.map (CommRingCat.ofHom (algebraMap R S))
  SchemeOverlapDiagonalChart.DiagonalCompatible (Limits.pullback.fst p p)
    (Limits.pullback.snd p p) (Limits.pullback.diagonal p)
    (Limits.pullback.diagonal_fst p) (Limits.pullback.diagonal_snd p) M e

/-- Tensor-chart normalization preserves and detects the geometric diagonal identity. -/
theorem fromFiberProduct_diagonal_iff (e : FiberProductOverlap R S M) :
    DiagonalCompatible R S M (fromFiberProduct R S M e) ↔
      FiberProductDiagonal R S M e := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap R S))
  exact SchemeOverlapDiagonalChart.normalize_diagonal_iff
    (Limits.pullback.fst p p) (Limits.pullback.snd p p) (pullbackSpecIso R S S).inv
    (Spec.map (CommRingCat.ofHom (left R S))) (Spec.map (CommRingCat.ofHom (right R S)))
    (pullbackSpecIso_inv_fst R S S) (pullbackSpecIso_inv_snd R S S)
    (Limits.pullback.diagonal p) (Spec.map (CommRingCat.ofHom (diagonalRing R S)))
    (diagonal_chart_inv R S) (Limits.pullback.diagonal_fst p)
    (Limits.pullback.diagonal_snd p) (diagonal_first R S) (diagonal_second R S) M e

/-- Reconstructing a categorical overlap preserves the supplied affine diagonal law. -/
theorem toFiberProduct_diagonal (e : Overlap R S M) (he : DiagonalCompatible R S M e) :
    FiberProductDiagonal R S M (toFiberProduct R S M e) := by
  apply (fromFiberProduct_diagonal_iff R S M _).mp
  simpa only [fromFiberProduct_toFiberProduct] using he

end FLT.Mazur.AffineGeometricOverlap
