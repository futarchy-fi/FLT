/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluInfinityScaledY

/-!
# The target cubic equation on the explicit infinity neighborhood

Faithful generic comparison descends the homogeneous equation to the actual
regular functions. The scaled target ordinate is nonzero generically.
-/

@[expose] public noncomputable section

open RatFunc FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

/-- The original image ordinate is nonzero, detected by its regular scaled value. -/
theorem infinityImageY_ne_zero :
    liftY E (curve E G) (xFunction E G) (slopeFunction E G) ≠ 0 := by
  have h : infinityKernelHom E G (infinityScaledY E G) ≠ 0 := by
    simpa only [map_zero] using
      (infinityKernelHom_injective E G).ne (infinityScaledY_ne_zero E G)
  rw [infinityScaledY_generic] at h
  exact (div_ne_zero_iff.mp h).1

/-- The scaled original functions satisfy the homogeneous target equation in their ring. -/
theorem infinityScaled_equation (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) :
    ((curve E G).map (algebraMap K (InfinityKernelRing E G))).toProjective.Equation
      ![infinityScaledX E G, infinityScaledY E G, infinityV E G] := by
  apply (Projective.map_equation _ (infinityKernelHom_injective E G) _).mp
  have hc : (infinityKernelHom E G).toRingHom.comp
      (algebraMap K (InfinityKernelRing E G)) = algebraMap K (FunctionField E) := by
    apply RingHom.ext
    intro c
    exact (infinityKernelHom E G).commutes c
  simp only [Projective.map, WeierstrassCurve.map_map, hc]
  have he := (Projective.equation_some _ _).mpr (velu_lift_equation E G hodd)
  have hs := ((curve E G).map (algebraMap K (FunctionField E))).toProjective.equation_smul
    (![liftX E (xFunction E G),
      liftY E (curve E G) (xFunction E G) (slopeFunction E G), 1])
    (isUnit_iff_ne_zero.mpr (inv_ne_zero (sourceGenericY_ne_zero E)))
  have hv : (infinityKernelHom E G).toRingHom ∘
      ![infinityScaledX E G, infinityScaledY E G, infinityV E G] =
      (liftY E E RatFunc.X 1)⁻¹ • ![liftX E (xFunction E G),
        liftY E (curve E G) (xFunction E G) (slopeFunction E G), 1] := by
    funext i
    fin_cases i <;>
      simp [infinityScaledX_generic, infinityScaledY_generic,
        infinityV_generic, div_eq_mul_inv, mul_comm]
  rw [hv]
  exact hs.mpr he

end WeierstrassCurve.Velu
