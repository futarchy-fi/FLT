/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSmallRamificationTorsion

/-!
# Actual torsion specialization under small ramification

Smooth reduction distinguishes p-torsion points on every integral equation,
including singular special fibers. Every affine p-torsion point has integral
coordinates, a useful constraint for descent through the explicit S2a scaling.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  [IsAdicComplete (maximalIdeal A) A] [IsDiscreteValuationRing A]
  (p : ℕ) [Fact p.Prime] (hp0 : (p : A) ≠ 0)
  (he : RaynaudParameters.order (p : A) < p - 1)

include hp0 he

/-- A p-torsion point reduces to infinity exactly when it is the identity. -/
theorem infinityReduction_prime_torsion_iff
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : p • P = 0) :
    InfinityReduction A W P ↔ P = 0 := by
  constructor
  · intro hinf
    let Q : ellipticE1 A W := ⟨P, hinf⟩
    have hQ : p • Q = 0 := Subtype.ext hP
    exact congrArg (ellipticE1 A W).subtype
      ((ellipticE1_prime_nsmul_eq_zero_iff_small_ramification A W p hp0 he Q).mp hQ)
  · rintro rfl
    exact infinityReduction_zero A W

/-- Smooth reduction is injective on p-torsion even when the special cubic is singular. -/
theorem smoothReduction_prime_torsion_injective_small_ramification
    (P Q : ellipticE0 A W) (hP : p • P = 0) (hQ : p • Q = 0)
    (hred : smoothReductionHom A W P = smoothReductionHom A W Q) : P = Q := by
  have hr : smoothReductionHom A W (P - Q) = 0 := by rw [map_sub, hred, sub_self]
  have hinf := (mem_smoothReductionHom_ker_iff A W (P - Q)).mp hr
  have hn : p • (P - Q).val = 0 := by
    have h : p • (P - Q) = 0 := by rw [nsmul_sub, hP, hQ, sub_self]
    exact congrArg (ellipticE0 A W).subtype h
  have hz := (infinityReduction_prime_torsion_iff A W p hp0 he (P - Q).val hn).mp hinf
  exact sub_eq_zero.mp (Subtype.ext hz)

variable [DecidableEq K]

/-- Nonintegral affine coordinates cannot occur on p-torsion below the ramification bound. -/
theorem affine_prime_torsion_coordinates_integral {x y : K}
    (h : (W.map (algebraMap A K)).toAffine.Nonsingular x y)
    (hP : p • (Affine.Point.some x y h) = 0) : x ∈ A ∧ y ∈ A := by
  classical
  by_contra hxy
  have hinf := (infinityReduction_affine_iff A W h).mpr hxy
  let f := (Projective.Point.toAffineAddEquiv (W.map (algebraMap A K)).toProjective).symm
  have hn : p • f (.some x y h) = 0 := by rw [← map_nsmul, hP, map_zero]
  have hz := (infinityReduction_prime_torsion_iff A W p hp0 he _ hn).mp hinf
  have heq : Affine.Point.some x y h = 0 := f.injective (hz.trans (map_zero f).symm)
  cases heq

end FLT.Mazur
