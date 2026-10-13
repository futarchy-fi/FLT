/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassGeometricFourTorsion
public import FLT.EllipticCurve.NTorsionCardOfDifferential

/-!
# Geometric three-torsion of the actual Weierstrass scheme

The constructed scheme's field-point group is the classical affine elliptic
curve group. The proved three-division identity therefore counts its actual
three-torsion maps: there are nine over a separably closed field with three
invertible. This comparison retains the original scheme morphisms.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] [DecidableEq K]
  (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- The torsion comparison identifies the actual scheme maps, including the identity. -/
def integralThreeTorsionEquiv :
    {P : (W.map (algebraMap R K)).toAffine.Point // 3 • P = 0} ≃
      {P : integralGroupFieldPoints (K := K) W hΔ // P ^ 3 = 1} where
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
/-- There are exactly nine geometric three-torsion maps into the original smooth cubic. -/
theorem integralThreeTorsion_card [IsSepClosed K] (h3 : (3 : K) ≠ 0) :
    Nat.card {P : integralGroupFieldPoints (K := K) W hΔ // P ^ 3 = 1} = 3 ^ 2 := by
  classical
  let _ : W.IsElliptic := ⟨hΔ⟩
  rw [← Nat.card_congr (integralThreeTorsionEquiv (K := K) W hΔ)]
  exact (W.map (algebraMap R K)).card_torsion_of_divisionDifferentialDefect h3
    (W.map (algebraMap R K)).divisionDifferentialDefect_three

end FLT.Mazur.WeierstrassIntegralChart
