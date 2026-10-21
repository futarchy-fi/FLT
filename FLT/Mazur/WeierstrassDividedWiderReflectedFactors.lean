/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReflectedBranchData
public import FLT.Mazur.WeierstrassDilatationDepthTransition

/-!
# Exact coefficient factors for the wider reflected numerator

The common ordinate scale is k; the numerator scale is 2*(k+l)-m.
All identities hold over the original coefficient ring, before specialization.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {k l m : ℕ} (D : SplitNodeDepth W π m)
  (d : Data W π k) (hkl : k ≤ l) (hm : k + 2 * l ≤ m)
  (htop : m ≤ 2 * (k + l)) (z : Data W π (m - k - l))

omit [IsDomain R] [IsLocalRing R] in
include hkl hm htop in
/-- The square of the common intercept scale factors through the reflected numerator. -/
theorem widerReflected_square_factor :
    (π ^ l) ^ 2 = π ^ (l - k) * π ^ (m - k - l) * π ^ (2 * (k + l) - m) := by
  rw [← pow_mul, ← pow_add, ← pow_add]
  congr 1
  omega

omit [IsDomain R] [IsLocalRing R] in
include hm htop in
/-- The original intercept scale is the reflected scale times the numerator scale. -/
theorem widerReflected_intercept_factor :
    π ^ k * π ^ l = π ^ (m - k - l) * π ^ (2 * (k + l) - m) := by
  rw [← pow_add, ← pow_add]
  congr 1
  omega

include D hkl hm in
/-- The linear intercept coefficient has exactly the Vieta cancellation factor. -/
theorem widerReflected_third_factor :
    d.b3 * π ^ l = π ^ (l - k) * π ^ (m - k - l) * z.b3 := by
  rw [depth_coefficient_factor π k (m - k - l) D.uniformizer_ne_zero
    (by omega) d.factor3 z.factor3]
  calc
    π ^ (m - k - l - k) * z.b3 * π ^ l =
        π ^ (m - k - l - k + l) * z.b3 := by rw [pow_add]; ring
    _ = π ^ (l - k) * π ^ (m - k - l) * z.b3 := by
      rw [← pow_add]
      congr 2
      omega

/-- The constant is the unit quotient at the exact original node depth. -/
theorem widerReflected_sixth_factor :
    d.b6 = π ^ (l - k) * π ^ (m - k - l) *
      reflectedBranchConstant D d hkl (by omega : 2 * l ≤ m) := by
  rw [reflectedBranchConstant_factor D d hkl (by omega), ← pow_add]
  congr 2
  omega

end FLT.Mazur.WeierstrassDividedDepth
