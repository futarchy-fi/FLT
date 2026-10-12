/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentBoundaryGeometry

/-!
# Inverse corrected boundary attachments

The whole inverse corrected horizontal transition recovers the original
preceding attachment with the original multiplicative scale retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ}
  (d : Data W π (k + 1)) (e : Data W π (k + 1 + 1))
local notation "E" => Scheme.Spec.mapIso
  (Iso.op (RingEquiv.toCommRingCatIso
    (AlgEquiv.toRingEquiv (adjacentBoundaryEquiv hπ d e))))

/-- The inverse corrected transition is precisely the original preceding attachment. -/
@[reassoc] theorem adjacentBoundary_inverse_previousToX :
    (E).inv ≫ horizontalOpenInclusion W (π ^ (k + 1)) π e.b3 e.b4 e.b6 =
      (nextBoundaryIso d).inv ≫ previousToX hπ d e := by
  have h := adjacentBoundaryEquiv_previousToX hπ d e
  change (E).hom ≫ (nextBoundaryIso d).inv ≫ previousToX hπ d e = _ at h
  rw [← h, Iso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
