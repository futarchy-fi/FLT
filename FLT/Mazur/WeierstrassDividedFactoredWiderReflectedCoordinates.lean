/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCommonSumCoordinates
public import FLT.Mazur.WeierstrassDividedFactoredCommonBranchOrdinate
public import FLT.Mazur.WeierstrassDividedOwnSumDepthCoordinates
public import FLT.Mazur.WeierstrassDividedWiderReflectedFormula
public import FLT.Mazur.WeierstrassDividedWiderReflectedFactors
public import FLT.Mazur.WeierstrassDividedUnequalDepthSecant

/-!
# Wider reflected coordinates with a finite quadratic coefficient quotient

Retain the full quadratic term in both common-scale branch ordinates.
A factorization of the second coefficient at depth k suffices throughout
k+2*l ≤ m ≤ 2*(k+l). Both coordinates contract to the original secant.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsLocalRing R] [Module.Flat R S] {W : WeierstrassCurve R} {π : R} {k l m : ℕ}
  (D : SplitNodeDepth W π m)
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (hm : k + 2 * l ≤ m)
  (z : Data W π (m - k - l))
  (b2 : R) (h2 : W.a₂ = π ^ k * b2)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "s" => algebraMap R S (π ^ k)
local notation "t" => algebraMap R S (π ^ (l - k))
local notation "x₁" => a (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "y₁" => a (y W (π ^ k) d.b3 d.b4 d.b6)
local notation "x₂" => c (x W (π ^ l) e.b3 e.b4 e.b6)
local notation "y₂" => c (y W (π ^ l) e.b3 e.b4 e.b6)
local notation "W'" => W.map (algebraMap R S)
variable (hc : IsUnit (a (y W (π ^ k) d.b3 d.b4 d.b6) +
    algebraMap R S W.a₁ * a (x W (π ^ k) d.b3 d.b4 d.b6) + algebraMap R S d.b3))
  (hd : IsUnit (c (y W (π ^ l) e.b3 e.b4 e.b6) +
    algebraMap R S W.a₁ * c (x W (π ^ l) e.b3 e.b4 e.b6) + algebraMap R S e.b3))
  (hxu : IsUnit (a (x W (π ^ k) d.b3 d.b4 d.b6) *
    c (x W (π ^ l) e.b3 e.b4 e.b6))) (i L : S)
local notation "dd" => commonBranchData (k := k) D d (by omega : k + 2 * k ≤ m)
local notation "ee" => commonBranchData D e hm
local notation "q" => factoredCommonBranchOrdinate d dd b2 a hc
local notation "r" => factoredCommonBranchOrdinate e ee b2 c hd
local notation "b" => sumDepthIntercept 1 x₁ x₂ q r i

local notation "v" => algebraMap R S (π ^ (2 * (k + l) - m))
local notation "C" => algebraMap R S
  (reflectedBranchConstant D d hkl ((Nat.le_add_left (2 * l) k).trans hm))

/-- The abscissa is constructed from the two actual branch-ordinate quotients. -/
def nodeFactoredWiderReflectedX : S :=
  reflectedBranchX v (algebraMap R S z.b3) C x₁ x₂ q r i hxu

/-- The ordinate uses the same wider numerator scale. -/
def nodeFactoredWiderReflectedY : S :=
  reflectedBranchY W' v v (algebraMap R S z.b3) C (algebraMap R S z.b3)
    x₁ x₂ q r i L hxu

local notation "X" => nodeFactoredWiderReflectedX D d e hkl hm z b2 a c hc hd hxu i
local notation "Y" => nodeFactoredWiderReflectedY D d e hkl hm z b2 a c hc hd hxu i L
variable (hi : i * (a (x W (π ^ k) d.b3 d.b4 d.b6) -
    algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6)) = 1)
  (hL : L * (a (x W (π ^ k) d.b3 d.b4 d.b6) -
    algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6)) =
      a (y W (π ^ k) d.b3 d.b4 d.b6) -
        algebraMap R S (π ^ (l - k)) * c (y W (π ^ l) e.b3 e.b4 e.b6))

omit [Module.Flat R S] in
include h2 hi hL in
/-- The common quotients construct the original divided intercept. -/
theorem nodeFactoredWiderReflected_intercept :
    y₁ - L * x₁ = algebraMap R S (π ^ l) * b := by
  have h := commonSumDepthIntercept_scale s t x₁ y₁ x₂ y₂ q r i L hi hL
    (factoredCommonBranchOrdinate_scale d dd b2 a hc le_rfl h2)
    (factoredCommonBranchOrdinate_scale e ee b2 c hd hkl h2)
  rwa [← map_mul, ← pow_add, Nat.add_sub_of_le hkl] at h

variable (htop : m ≤ 2 * (k + l))

include htop h2 hi hL in
/-- The wider reflected abscissa scales to the entire original secant abscissa. -/
theorem nodeFactoredWiderReflectedX_scale :
    algebraMap R S (π ^ (m - k - l)) * X =
      (W').toAffine.addX (s * x₁) (s * (t * x₂)) L := by
  apply widerReflectedX_scale W' s t (algebraMap R S (π ^ l))
    (algebraMap R S (π ^ (m - k - l))) v (algebraMap R S d.b3)
    (algebraMap R S d.b6) (algebraMap R S z.b3) C x₁ y₁ x₂ q r i L hxu
  · exact WeierstrassIntegralChart.flatRingHom_isRegular _
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
      (isRegular_iff_ne_zero.mpr (pow_ne_zero _ D.uniformizer_ne_zero))
  · exact nodeFactoredWiderReflected_intercept D d e hkl hm b2 h2 a c hc hd i L hi hL
  · simpa only [map_mul, map_pow] using
      congrArg (algebraMap R S) (widerReflected_square_factor (π := π) hkl hm htop)
  · simpa only [map_mul] using
      congrArg (algebraMap R S) (widerReflected_third_factor D d hkl hm z)
  · simpa only [map_mul] using
      congrArg (algebraMap R S) (widerReflected_sixth_factor D d hkl hm htop)
  · have he := equation_map W (π ^ k) d.b3 d.b4 d.b6
      (unequalDepthRight D.uniformizer_ne_zero d e hkl c)
    simp only [unequalDepthRight_x, unequalDepthRight_y] at he
    exact divided_secant_product W' s (algebraMap R S d.b3)
      (algebraMap R S d.b4) (algebraMap R S d.b6) x₁ y₁ (t * x₂) (t * y₂) L
      (equation_map W (π ^ k) d.b3 d.b4 d.b6 a) he
      (isUnit_iff_exists_inv.mpr ⟨i, by rwa [mul_comm]⟩) hL

include htop h2 hi hL in
/-- The ordinate contracts with exactly the same reflected depth. -/
theorem nodeFactoredWiderReflectedY_scale :
    algebraMap R S (π ^ (m - k - l)) * Y =
      (W').toAffine.addY (s * x₁) (s * (t * x₂)) (s * y₁) L := by
  apply widerReflectedY_scale W' s t (algebraMap R S (π ^ l))
    (algebraMap R S (π ^ (m - k - l))) v (algebraMap R S z.b3) C
    x₁ y₁ x₂ q r i L hxu
  · rw [WeierstrassCurve.map_a₃, z.factor3, map_mul]
  · exact nodeFactoredWiderReflected_intercept D d e hkl hm b2 h2 a c hc hd i L hi hL
  · simpa only [map_mul] using congrArg (algebraMap R S)
      (widerReflected_intercept_factor (π := π) hm htop)
  · exact nodeFactoredWiderReflectedX_scale D d e hkl hm z b2 h2 a c hc hd hxu i L hi hL htop

end FLT.Mazur.WeierstrassDividedDepth
