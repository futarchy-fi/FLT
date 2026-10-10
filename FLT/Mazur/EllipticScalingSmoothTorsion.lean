/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticScaledTorsionReduction
public import FLT.Mazur.EllipticVariableChangeSmoothness

/-!
# Smooth prime torsion excludes positive scaling

An actual point is transported through the given generic variable change.
Small ramification makes its coordinates on the scaled equation integral;
positive scaling would send it into the original singular special-fiber origin.
Thus every smooth prime-torsion point on the original equation is zero.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] [DecidableEq K]
  (A : ValuationSubring K) [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A] (W U : WeierstrassCurve A)
  [(W.map (algebraMap A K)).IsElliptic]

/-- Positive generic scaling is incompatible with a nonzero smooth prime-torsion point. -/
theorem smooth_prime_torsion_eq_zero_of_scaling
    (h3 : W.a₃ ∈ maximalIdeal A) (h4 : W.a₄ ∈ maximalIdeal A)
    (p : ℕ) [Fact p.Prime] (hp0 : (p : A) ≠ 0)
    (he : RaynaudParameters.order (p : A) < p - 1)
    (u : A) (hu : u ∈ maximalIdeal A) (C : VariableChange K)
    (hC : C • W.map (algebraMap A K) = U.map (algebraMap A K))
    (hCu : (C.u : K) = u) (hCr : C.r = 0) (hCs : C.s = 0) (hCt : C.t = 0)
    (P : (W.map (algebraMap A K)).toAffine.Point) (hP : p • P = 0)
    (hsm : SmoothReduction A W P.toProjective) : P = 0 := by
  let e := (Affine.Point.equivOfEq hC.symm).trans
    (Affine.Point.equivVariableChange (W.map (algebraMap A K)) C)
  obtain ⟨Q, rfl⟩ := e.surjective P
  have hQ : p • Q = 0 := e.injective (by rw [map_nsmul, hP, map_zero])
  cases Q with
  | zero => exact map_zero e
  | some x y h =>
    have hv := (variableChange_nonsingular (W.map (algebraMap A K)) C x y).mpr
      (hC.symm ▸ h)
    simp only [hCu, hCr, hCs, hCt, mul_zero, zero_mul, add_zero] at hv
    have heq : e (.some x y h) = Affine.Point.some _ _ hv := by
      dsimp only [e]
      rw [AddEquiv.trans_apply, Affine.Point.equivOfEq_some,
        Affine.Point.equivVariableChange_some]
      apply Affine.Point.some_eq_some <;>
        simp only [hCu, hCr, hCs, hCt, mul_zero, zero_mul, add_zero]
    rw [heq] at hsm
    exact False.elim
      (not_smoothReduction_weighted_prime_torsion A W h3 h4 U p hp0 he u hu h hQ hv hsm)

end FLT.Mazur
