/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentIntegralBoundary

/-!
# The original boundary square in localization coordinates

Normalize both boundary projections before applying tensor base change.
The target is arbitrary, so the proof need not unfold any retained models.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {k : ℕ} (e : Data W π (k + 1)) (f : Data W π (k + 1 + 1))
  {X : Scheme} (i : stepX e ⟶ X) (j : stepX f ⟶ X)
open WeierstrassSuccessiveX

/-- Replacing both original projections by their full localization formulas is cartesian. -/
theorem localizedBoundary_isPullback (H : IsPullback (nextToX e) (previousToX hπ e f) i j) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (depthOverlapEquiv W π k e.b3 e.b4 e.b6).symm.toRingHom) ≫
          xOpenInclusion W (π ^ k) π e.b3 e.b4 e.b6)
      (Spec.map (CommRingCat.ofHom (previousBoundaryEquiv hπ e f).symm.toRingHom) ≫
        horizontalOpenInclusion W (π ^ (k + 1)) π f.b3 f.b4 f.b6) i j := by
  erw [depthOverlap_inverse_inclusion e, previousBoundary_inverse_inclusion hπ e f]
  exact H

end FLT.Mazur.WeierstrassDividedDepth
