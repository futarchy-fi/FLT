/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteAffineProper

/-!
# The actual affine contraction on every divided depth

The finite contraction retains the original affine coordinate map on its
divided chart, before the open immersion into the projective cubic.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (d : Data W π k)

/-- The original affine coordinate map of the actual depth chart. -/
def toAffine : chart d ⟶ Spec (.of (WeierstrassIntegralChart.Coordinate W 2)) :=
  Spec.map (CommRingCat.ofHom (WeierstrassDilatation.fromOriginal
    W (π ^ k) d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6).toRingHom)

/-- The affine contraction retains its original projective-cubic map. -/
@[reassoc] theorem toAffine_toCurve :
    toAffine d ≫ WeierstrassIntegralChart.integralCurveChart W 2 = toCurve d := rfl

/-- The initial whole contraction restricts to the actual divided affine coordinate map. -/
@[reassoc] theorem initialToAffine_divided :
    (initialExterior d).dividedChart ≫ initialToAffine d = toAffine d := by
  rw [← cancel_mono (WeierstrassIntegralChart.integralCurveChart W 2), Category.assoc,
    initialToAffine_toCurve, initialToCurve_divided, toAffine_toCurve]

variable [IsDomain R] (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))

/-- Every finite whole affine contraction retains its final divided coordinate map. -/
@[reassoc] theorem finiteDivided_toAffine (j : ℕ) (hj : j ≤ n) :
    (finiteExterior hπ data (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j hj).dividedChart ≫
        finiteToAffine hπ data j hj = toAffine (data ⟨j, Nat.lt_succ_of_le hj⟩) := by
  rw [← cancel_mono (WeierstrassIntegralChart.integralCurveChart W 2), Category.assoc,
    finiteToAffine_toCurve, finiteDivided_toCurve, toAffine_toCurve]

end FLT.Mazur.WeierstrassDividedDepth
