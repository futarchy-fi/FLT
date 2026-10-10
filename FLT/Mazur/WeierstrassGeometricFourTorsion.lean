/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassProjectiveGroupComparison
public import FLT.EllipticCurve.NTorsionCardOfDifferential

/-!
# Geometric four-torsion of the actual Weierstrass scheme

The constructed scheme's field-point group is the classical affine elliptic
curve group. The proved four-division identity therefore counts its actual
four-torsion maps: there are sixteen over a separably closed field with two
invertible. This comparison retains the original scheme morphisms.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] [DecidableEq K]
  (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- Affine elliptic points are the actual field-valued points of the constructed group scheme. -/
def integralAffinePointAddEquiv :
    (W.map (algebraMap R K)).toAffine.Point ≃+
      Additive (integralGroupFieldPoints (K := K) W hΔ) :=
  (Projective.Point.toAffineAddEquiv (W.map (algebraMap R K)).toProjective).symm.trans
    (integralProjectivePointAddEquiv W hΔ)

/-- The torsion comparison identifies the actual scheme maps, including the identity. -/
def integralFourTorsionEquiv :
    {P : (W.map (algebraMap R K)).toAffine.Point // 4 • P = 0} ≃
      {P : integralGroupFieldPoints (K := K) W hΔ // P ^ 4 = 1} where
  toFun P := ⟨(integralAffinePointAddEquiv W hΔ P.val).toMul, by
    have h := congrArg (integralAffinePointAddEquiv (K := K) W hΔ) P.property
    simpa only [map_nsmul, map_zero, toMul_nsmul, toMul_zero]
      using congrArg Additive.toMul h⟩
  invFun P := ⟨(integralAffinePointAddEquiv W hΔ).symm (Additive.ofMul P.val), by
    apply (integralAffinePointAddEquiv W hΔ).injective
    simpa only [map_nsmul, map_zero, AddEquiv.apply_symm_apply,
      ofMul_pow, ofMul_one] using congrArg Additive.ofMul P.property⟩
  left_inv P := Subtype.ext ((integralAffinePointAddEquiv W hΔ).symm_apply_apply P.val)
  right_inv P := Subtype.ext (congrArg Additive.toMul
    ((integralAffinePointAddEquiv W hΔ).apply_symm_apply (Additive.ofMul P.val)))

omit [DecidableEq K] in
/-- There are exactly sixteen geometric four-torsion maps into the original smooth cubic. -/
theorem integralFourTorsion_card [IsSepClosed K] (h2 : (2 : K) ≠ 0) :
    Nat.card {P : integralGroupFieldPoints (K := K) W hΔ // P ^ 4 = 1} = 4 ^ 2 := by
  classical
  let _ : W.IsElliptic := ⟨hΔ⟩
  have h4 : (4 : K) ≠ 0 := by
    simpa only [show (4 : K) = 2 ^ 2 by ring] using pow_ne_zero 2 h2
  rw [← Nat.card_congr (integralFourTorsionEquiv (K := K) W hΔ)]
  exact (W.map (algebraMap R K)).card_torsion_of_divisionDifferentialDefect h4
    (W.map (algebraMap R K)).divisionDifferentialDefect_four

end FLT.Mazur.WeierstrassIntegralChart
