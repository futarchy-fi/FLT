/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassInfinityAdditionFormula
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Square-zero coordinates at the Weierstrass identity

An infinitesimal point reducing to infinity has Y-chart coordinates (x,1,0).
The regular infinity addition formula adds the x coordinates on a square-zero
ideal. Both denominators are units, so this is an actual chart computation.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  (I : Ideal R) (hI : I ^ 2 = ⊥)

include hI

/-- Products of two square-zero infinitesimal coordinates vanish. -/
theorem squareZero_mul {x y : R} (hx : x ∈ I) (hy : y ∈ I) : x * y = 0 := by
  have h := Ideal.mul_mem_mul hx hy
  rw [← pow_two, hI, Ideal.mem_bot] at h
  exact h

/-- The cubic equation forces the infinitesimal Z coordinate to vanish. -/
theorem infinitySquareZero_z {x z : R} (hx : x ∈ I) (hz : z ∈ I)
    (hP : W.toProjective.Equation ![x, 1, z]) : z = 0 := by
  have hx2 : x ^ 2 = 0 := by simpa only [pow_two] using squareZero_mul I hI hx hx
  have hz2 : z ^ 2 = 0 := by simpa only [pow_two] using squareZero_mul I hI hz hz
  have hxz := squareZero_mul I hI hx hz
  rw [Projective.equation_iff] at hP
  simp only [Projective.fin3_def_ext] at hP
  simpa [pow_succ, ← mul_assoc, hx2, hz2, pow_two, mul_assoc, hxz,
    squareZero_mul I hI hx hx, squareZero_mul I hI hz hz] using hP

/-- The divided-difference numerator vanishes on two infinitesimal points. -/
theorem infinitySquareZero_numerator {x y : R} (hx : x ∈ I) (hy : y ∈ I) :
    infinitySlopeNumerator W x y 0 = 0 := by
  simp [infinitySlopeNumerator, pow_two, squareZero_mul I hI hx hx,
    squareZero_mul I hI hx hy, squareZero_mul I hI hy hy]

/-- The slope denominator remains invertible on the whole square-zero neighborhood. -/
theorem infinitySquareZero_denominator {y : R} (hy : y ∈ I) :
    IsUnit (infinitySlopeDenominator W y 0 0) := by
  have hy2 := squareZero_mul I hI hy hy
  have hn : IsNilpotent (W.a₁ * y) := ⟨2, by rw [mul_pow, pow_two y, hy2, mul_zero]⟩
  simpa [infinitySlopeDenominator, pow_two, hy2] using hn.isUnit_one_add

omit hI in
/-- With zero slope, the regular homogeneous formula has explicit linear coordinates. -/
theorem infinityAdditionXYZ_zero_slope (x y : R) :
    infinityAdditionXYZ W x y 0 0 = ![x + y, 1 - W.a₁ * (x + y), 0] := by
  ext i
  fin_cases i <;>
    simp [infinityAdditionXYZ, lineThird, cubicPolar, Projective.eval_polynomial,
      Projective.negY] <;> ring

/-- The output Y coordinate is a unit on the square-zero identity neighborhood. -/
theorem infinitySquareZero_output_unit {x y : R} (hx : x ∈ I) (hy : y ∈ I) :
    IsUnit (infinityAdditionXYZ W x y 0 0 1) := by
  have hs := squareZero_mul I hI (I.add_mem hx hy) (I.add_mem hx hy)
  have hn : IsNilpotent (W.a₁ * (x + y)) := ⟨2, by rw [mul_pow, pow_two (x + y), hs, mul_zero]⟩
  simpa [infinityAdditionXYZ_zero_slope] using hn.isUnit_one_sub

/-- After normalizing Y, addition is exactly addition of the infinitesimal X coordinates. -/
theorem infinitySquareZero_normalized {x y u : R} (hx : x ∈ I) (hy : y ∈ I)
    (hu : u * infinityAdditionXYZ W x y 0 0 1 = 1) :
    u • infinityAdditionXYZ W x y 0 0 = ![x + y, 1, 0] := by
  have hs := squareZero_mul I hI (I.add_mem hx hy) (I.add_mem hx hy)
  rw [infinityAdditionXYZ_zero_slope] at hu ⊢
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hu
  ext i
  fin_cases i
  · change u * (x + y) = x + y
    linear_combination (x + y) * hu + u * W.a₁ * hs
  · exact hu
  · exact mul_zero u

end FLT.Mazur.WeierstrassIntegralChart
