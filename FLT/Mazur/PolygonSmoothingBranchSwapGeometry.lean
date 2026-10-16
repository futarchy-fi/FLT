/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingRingMapBranch

/-!
# Reversing the orientation of an entire smoothing chart

The actual branch interchange exchanges the two full punctures. The reciprocal
edge parameter records the orientation change needed on the second retained arm.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonSmoothing
variable (R : Type*) [CommRing R] (t : R)

/-- Interchange the full node coordinates on spectra. -/
def branchSwapIso : chart R t ≅ chart R t :=
  Scheme.Spec.mapIso (branchSwap t).toRingEquiv.toCommRingCatIso.op

/-- Interchange is involutive on the actual scheme. -/
@[reassoc] theorem branchSwapIso_involutive :
    (branchSwapIso R t).hom ≫ (branchSwapIso R t).hom = 𝟙 _ :=
  (branchSwapIso R t).hom_inv_id

/-- The full left puncture becomes the full right puncture with unchanged parameter. -/
@[reassoc] theorem leftBranchOpen_branchSwapIso :
    leftBranchOpen R t ≫ (branchSwapIso R t).hom = rightBranchOpen R t := by
  rw [leftBranchOpen_eq_spec, rightBranchOpen_eq_spec]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

/-- The full right puncture becomes the full left puncture. -/
@[reassoc] theorem rightBranchOpen_branchSwapIso :
    rightBranchOpen R t ≫ (branchSwapIso R t).hom = leftBranchOpen R t := by
  rw [← leftBranchOpen_branchSwapIso R t, Category.assoc,
    branchSwapIso_involutive, Category.comp_id]

/-- The incoming cyclic edge becomes the reciprocal outgoing edge. -/
@[reassoc] theorem precedingBranch_branchSwapIso :
    precedingBranch R t ≫ (branchSwapIso R t).hom =
      (edgeInversion R).hom ≫ leftBranchOpen R t := by
  rw [precedingBranch, Category.assoc, rightBranchOpen_branchSwapIso]

/-- Reversing an outgoing edge retains the reciprocal incoming parameter. -/
@[reassoc] theorem leftBranchOpen_branchSwapIso_preceding :
    leftBranchOpen R t ≫ (branchSwapIso R t).hom =
      (edgeInversion R).inv ≫ precedingBranch R t := by
  rw [leftBranchOpen_branchSwapIso, precedingBranch,
    Iso.inv_hom_id_assoc]

end FLT.Mazur.PolygonSmoothing
