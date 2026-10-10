/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassAffineNormalForm

/-!
# Uniqueness and invertibility of triangular affine coordinates

Normal-form uniqueness detects all three low-pole coefficients over arbitrary
rings. Two inverse triangular coordinate maps therefore have unit leading terms.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W V : WeierstrassCurve R)

/-- The original functions 1, x, y have unique coefficients over the base ring. -/
theorem lowCoordinate_injective {r s t r' s' t' : R}
    (h : algebraMap R _ r + algebraMap R _ s * coord W 2 0 +
        algebraMap R _ t * coord W 2 1 =
      algebraMap R _ r' + algebraMap R _ s' * coord W 2 0 +
        algebraMap R _ t' * coord W 2 1) : r = r' ∧ s = s' ∧ t = t' := by
  have hn : affineNormalForm W (C r + C s * X) (C t) =
      affineNormalForm W (C r' + C s' * X) (C t') := by
    simpa [affineNormalForm] using h
  obtain ⟨hp, hq⟩ := affineNormalForm_injective W hn
  refine ⟨?_, ?_, C_injective hq⟩
  · simpa using congrArg (fun p : R[X] => p.coeff 0) hp
  · simpa using congrArg (fun p : R[X] => p.coeff 1) hp

/-- Composing triangular maps recovers both leading coefficients multiplicatively. -/
theorem triangular_leftInverse_coefficients
    (f : Coordinate V 2 →ₐ[R] Coordinate W 2)
    (g : Coordinate W 2 →ₐ[R] Coordinate V 2) (hgf : Function.LeftInverse g f)
    (r s t v w r' s' t' v' w' : R)
    (hx : f (coord V 2 0) = algebraMap R _ r + algebraMap R _ s * coord W 2 0)
    (hy : f (coord V 2 1) = algebraMap R _ t + algebraMap R _ v * coord W 2 0 +
      algebraMap R _ w * coord W 2 1)
    (hx' : g (coord W 2 0) = algebraMap R _ r' + algebraMap R _ s' * coord V 2 0)
    (hy' : g (coord W 2 1) = algebraMap R _ t' + algebraMap R _ v' * coord V 2 0 +
      algebraMap R _ w' * coord V 2 1) : s * s' = 1 ∧ w * w' = 1 := by
  have hxx := hgf (coord V 2 0)
  rw [hx, map_add, map_mul, g.commutes, g.commutes, hx'] at hxx
  have hyy := hgf (coord V 2 1)
  rw [hy, map_add, map_add, map_mul, map_mul, g.commutes, g.commutes,
    g.commutes, hx', hy'] at hyy
  constructor
  · have h : algebraMap R _ (r + s * r') +
        algebraMap R _ (s * s') * coord V 2 0 + algebraMap R _ 0 * coord V 2 1 =
        algebraMap R _ 0 + algebraMap R _ 1 * coord V 2 0 +
          algebraMap R _ 0 * coord V 2 1 := by
      simpa only [map_add, map_mul, map_zero, map_one, zero_mul, add_zero,
        zero_add, one_mul, mul_add, mul_assoc, add_assoc] using hxx
    exact (lowCoordinate_injective V h).2.1
  · have h : algebraMap R _ (t + v * r' + w * t') +
        algebraMap R _ (v * s' + w * v') * coord V 2 0 +
        algebraMap R _ (w * w') * coord V 2 1 =
        algebraMap R _ 0 + algebraMap R _ 0 * coord V 2 0 +
          algebraMap R _ 1 * coord V 2 1 := by
      simp only [map_add, map_mul, map_zero, map_one, zero_mul, zero_add, one_mul]
      linear_combination hyy
    exact (lowCoordinate_injective V h).2.2

/-- A triangular map with triangular left inverse has invertible x and y scales. -/
theorem triangular_leftInverse_isUnit
    (f : Coordinate V 2 →ₐ[R] Coordinate W 2)
    (g : Coordinate W 2 →ₐ[R] Coordinate V 2) (hgf : Function.LeftInverse g f)
    (r s t v w r' s' t' v' w' : R)
    (hx : f (coord V 2 0) = algebraMap R _ r + algebraMap R _ s * coord W 2 0)
    (hy : f (coord V 2 1) = algebraMap R _ t + algebraMap R _ v * coord W 2 0 +
      algebraMap R _ w * coord W 2 1)
    (hx' : g (coord W 2 0) = algebraMap R _ r' + algebraMap R _ s' * coord V 2 0)
    (hy' : g (coord W 2 1) = algebraMap R _ t' + algebraMap R _ v' * coord V 2 0 +
      algebraMap R _ w' * coord V 2 1) : IsUnit s ∧ IsUnit w := by
  obtain ⟨hs, hw⟩ := triangular_leftInverse_coefficients W V f g hgf
    r s t v w r' s' t' v' w' hx hy hx' hy'
  exact ⟨isUnit_iff_exists_inv.mpr ⟨s', hs⟩, isUnit_iff_exists_inv.mpr ⟨w', hw⟩⟩

end FLT.Mazur.WeierstrassIntegralChart
