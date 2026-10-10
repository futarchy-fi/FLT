/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveReesProper
public import FLT.Mazur.WeierstrassSuccessiveXDepthComparison

/-!
# Proper local contraction at each actual divided depth

The proved proper local replacement remains proper after identifying its
target with the normalized preceding depth. This is the local map used by
the exterior iteration; gluing properness into the whole is a separate step.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] [IsDomain R]
  (π : R) (k : ℕ) (hπ : π ≠ 0) (W : WeierstrassCurve R)
  (b3 b4 b6 c3 c4 c6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6)
  (H3 : W.a₃ = π ^ (k + 1) * c3) (H4 : W.a₄ = π ^ (k + 1) * c4)
  (H6 : W.a₆ = (π ^ (k + 1)) ^ 2 * c6)

/-- The actual normalized local contraction at each successive depth is proper. -/
theorem depthContraction_isProper :
    IsProper (depthContraction π k hπ W b3 b4 b6 c3 c4 c6 h3 h4 h6 H3 H4 H6) := by
  let _ : IsProper (contraction W (π ^ k) π c3 c4 c6) :=
    WeierstrassSuccessiveRees.contraction_isProper W (π ^ k) π c3 c4 c6 hπ
  change IsProper (contraction W (π ^ k) π c3 c4 c6 ≫
    (Scheme.Spec.mapIso (previousDepthEquiv π k hπ W b3 b4 b6 c3 c4 c6
      h3 h4 h6 H3 H4 H6).toRingEquiv.toCommRingCatIso.op).hom)
  infer_instance

end FLT.Mazur.WeierstrassSuccessiveX
