/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticVariableChangeIntegrality
public import FLT.Mazur.EllipticVariableChangeSmoothness
public import FLT.Mazur.EllipticReductionRelation

/-!
# Integral variable changes preserve smooth reduction

On the integral affine chart this follows from the change of the two partial
derivatives after reduction. Outside that chart both points reduce to infinity,
since the change and its inverse have integral coefficients and unit u.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (C : VariableChange A)

/-- Smooth reduction of affine points is invariant under an integral unit variable change. -/
theorem smoothReduction_variableChange_affine (x y : K)
    (h : ((C • W).map (algebraMap A K)).toAffine.Nonsingular x y)
    (h' : (W.map (algebraMap A K)).toAffine.Nonsingular
      (((C.u : A) : K) ^ 2 * x + (C.r : K))
      (((C.u : A) : K) ^ 3 * y + ((C.u : A) : K) ^ 2 * (C.s : K) * x + (C.t : K))) :
    SmoothReduction A W (Affine.Point.toProjective (.some _ _ h')) ↔
      SmoothReduction A (C • W) (Affine.Point.toProjective (.some _ _ h)) := by
  by_cases hi : x ∈ A ∧ y ∈ A
  · let x₀ : A := ⟨x, hi.1⟩
    let y₀ : A := ⟨y, hi.2⟩
    let X : A := (C.u : A) ^ 2 * x₀ + C.r
    let Y : A := (C.u : A) ^ 3 * y₀ + (C.u : A) ^ 2 * C.s * x₀ + C.t
    change SmoothReduction A W (Affine.Point.toProjective (.some (X : K) (Y : K) h')) ↔ _
    rw [smoothReduction_affine_iff A W X Y, smoothReduction_affine_iff A (C • W) x₀ y₀]
    have hv := variableChange_nonsingular (W.map (residue A)) (C.map (residue A))
      (residue A x₀) (residue A y₀)
    rw [map_variableChange] at hv
    simpa only [X, Y, map_add, map_mul, map_pow, VariableChange.map,
      Units.coe_map, MonoidHom.coe_ofClass] using hv
  · have hi' := mt (variableChange_coordinates_mem_iff A C x y).mp hi
    exact iff_of_true (smoothReduction_of_nonintegral A W h' hi')
      (smoothReduction_of_nonintegral A (C • W) h hi)

end FLT.Mazur
