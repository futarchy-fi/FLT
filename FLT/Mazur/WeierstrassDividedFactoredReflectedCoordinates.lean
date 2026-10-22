/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReflectedBranchData
public import FLT.Mazur.WeierstrassDividedReflectedBranchFormula
public import FLT.Mazur.WeierstrassDividedFactoredCommonBranchOrdinate
public import FLT.Mazur.WeierstrassDividedUnequalDepthSecant

/-!
# Reflected coordinates retaining the second-coefficient quotient

Both branch ordinates include the quadratic coefficient term. A finite
factorization at the common residual depth replaces the zero-coefficient
hypothesis. Vieta still contracts the entire output to the original secant.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsLocalRing R] [Module.Flat R S] {W : WeierstrassCurve R} {π : R} {k l m : ℕ}
  (D : SplitNodeDepth W π m) (d : Data W π k) (e : Data W π l)
  (hkl : k ≤ l) (hl : 2 * l ≤ m) (hm : m ≤ k + 2 * l)
  (z : Data W π (m - k - l)) (b2 : R) (h2 : W.a₂ = π ^ (m - 2 * l) * b2)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "s" => algebraMap R S (π ^ k)
local notation "t" => algebraMap R S (π ^ (l - k))
local notation "v" => algebraMap R S (π ^ (m - 2 * l))
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
local notation "q" => factoredCommonBranchOrdinate d (reflectedLeftBranchData D d hkl hl) b2 a hc
local notation "r" => factoredCommonBranchOrdinate e
  (reflectedRightBranchData (k := k) D e hl) b2 c hd
local notation "b" => sumDepthIntercept 1 x₁ x₂ q r i
local notation "C" => algebraMap R S (reflectedBranchConstant D d hkl hl)

/-- The reflected abscissa is constructed from actual common-scale ordinates. -/
def nodeFactoredReflectedX : S := reflectedBranchX v (algebraMap R S e.b3) C x₁ x₂ q r i hxu

/-- The ordinate is at the same reflected output depth. -/
def nodeFactoredReflectedY : S :=
  reflectedBranchY W' s v (algebraMap R S e.b3) C (algebraMap R S z.b3)
    x₁ x₂ q r i L hxu

local notation "X" => nodeFactoredReflectedX D d e hkl hl b2 a c hc hd hxu i
local notation "Y" => nodeFactoredReflectedY D d e hkl hl z b2 a c hc hd hxu i L
variable (hi : i * (a (x W (π ^ k) d.b3 d.b4 d.b6) -
    algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6)) = 1)
  (hL : L * (a (x W (π ^ k) d.b3 d.b4 d.b6) -
    algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6)) =
      a (y W (π ^ k) d.b3 d.b4 d.b6) -
        algebraMap R S (π ^ (l - k)) * c (y W (π ^ l) e.b3 e.b4 e.b6))

omit [IsDomain R] [IsLocalRing R] [Module.Flat R S] in
include hkl hl in
/-- The common ordinate and relative input scales multiply to the reflected scale. -/
theorem nodeFactoredReflected_scale : t * v = algebraMap R S (π ^ (m - k - l)) := by
  rw [← map_mul, ← pow_add, show l - k + (m - 2 * l) = m - k - l by omega]

omit [Module.Flat R S] in
include hm h2 hi hL in
/-- The original chord constructs the reflected-scale intercept. -/
theorem nodeFactoredReflected_intercept : y₁ - L * x₁ = t * v * b := by
  rw [mul_comm t v]
  apply commonSumDepthIntercept_scale v t x₁ y₁ x₂ y₂ q r i L hi hL
  · exact factoredCommonBranchOrdinate_scale d _ b2 a hc (by omega) h2
  · exact factoredCommonBranchOrdinate_scale e _ b2 c hd (by omega) h2

include hm h2 hi hL in
/-- Vieta identifies the entire abscissa with the original secant after scaling. -/
theorem nodeFactoredReflectedX_scale :
    algebraMap R S (π ^ (m - k - l)) * X =
      (W').toAffine.addX (s * x₁) (s * (t * x₂)) L := by
  rw [← nodeFactoredReflected_scale hkl hl]
  apply reflectedBranchX_scale W' s t v (algebraMap R S e.b3) C x₁ y₁ x₂ q r i L hxu
  · exact WeierstrassIntegralChart.flatRingHom_isRegular _
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
      (isRegular_iff_ne_zero.mpr (pow_ne_zero _ D.uniformizer_ne_zero))
  · exact nodeFactoredReflected_intercept D d e hkl hl hm b2 h2 a c hc hd i L hi hL
  · have he := equation_map W (π ^ k) d.b3 d.b4 d.b6
      (unequalDepthRight D.uniformizer_ne_zero d e hkl c)
    simp only [unequalDepthRight_x, unequalDepthRight_y] at he
    have hp := divided_secant_product W' s (algebraMap R S d.b3)
      (algebraMap R S d.b4) (algebraMap R S d.b6) x₁ y₁ (t * x₂) (t * y₂) L
      (equation_map W (π ^ k) d.b3 d.b4 d.b6 a) he
      (isUnit_iff_exists_inv.mpr ⟨i, by rwa [mul_comm]⟩) hL
    have h3 : algebraMap R S d.b3 = t * algebraMap R S e.b3 := by
      rw [depth_coefficient_factor π k l D.uniformizer_ne_zero hkl d.factor3 e.factor3,
        map_mul]
    have h6 : algebraMap R S d.b6 = (t ^ 2 * v) * C := by
      rw [reflectedBranchConstant_factor D d hkl hl, map_mul]
      congr 1
      rw [← map_pow, ← map_mul, ← pow_mul, ← pow_add]
      congr 2
      omega
    rwa [h3, h6] at hp

include hm h2 hi hL in
/-- The reflected ordinate scales to the original secant ordinate. -/
theorem nodeFactoredReflectedY_scale :
    algebraMap R S (π ^ (m - k - l)) * Y =
      (W').toAffine.addY (s * x₁) (s * (t * x₂)) (s * y₁) L := by
  rw [← nodeFactoredReflected_scale hkl hl]
  apply reflectedBranchY_scale W' s t v (algebraMap R S e.b3) C
    (algebraMap R S z.b3) x₁ y₁ x₂ q r i L hxu
  · rw [WeierstrassCurve.map_a₃, z.factor3, map_mul, nodeFactoredReflected_scale hkl hl]
  · exact nodeFactoredReflected_intercept D d e hkl hl hm b2 h2 a c hc hd i L hi hL
  · rw [nodeFactoredReflected_scale hkl hl]
    exact nodeFactoredReflectedX_scale D d e hkl hl hm b2 h2 a c hc hd hxu i L hi hL

end FLT.Mazur.WeierstrassDividedDepth
