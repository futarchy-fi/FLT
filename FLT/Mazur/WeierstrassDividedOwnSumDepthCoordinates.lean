/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOwnBranchOrdinate
public import FLT.Mazur.WeierstrassDividedSumDepthFormula
public import FLT.Mazur.WeierstrassDividedUnequalDepthSecant

/-!
# Sum-depth coordinates from actual unequal-depth inputs

Construct both branch-ordinate quotients from doubled-depth coefficient
data, then form the sum-depth coordinates. All inverted elements are input
denominators; the uniformizer is only cancelled using flatness.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [Module.Flat R S] {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k l : ℕ}
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (dd : Data W π (k + k)) (ee : Data W π (l + l)) (z : Data W π (k + l))
  (h2 : W.a₂ = 0)
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
local notation "q" => ownBranchOrdinate d dd a hc
local notation "r" => ownBranchOrdinate e ee c hd
local notation "b" => sumDepthIntercept t x₁ x₂ q r i

omit [IsDomain R] [Module.Flat R S] in
include hkl in
/-- The sum-depth scale is the product of the original two depth scales. -/
theorem ownSumDepth_scale : s ^ 2 * t = algebraMap R S (π ^ (k + l)) := by
  rw [← map_pow, ← map_mul, ← pow_mul, ← pow_add]
  congr 2
  omega

omit [IsDomain R] [Module.Flat R S] in
include hkl in
/-- The deeper input scale is s*t. -/
theorem ownSumDepth_rightScale : s * t = algebraMap R S (π ^ l) := by
  rw [← map_mul, ← pow_add, Nat.add_sub_of_le hkl]

/-- The abscissa is constructed from the two actual branch-ordinate quotients. -/
def ownSumDepthX : S := sumDepthX t (algebraMap R S z.b3) (algebraMap R S z.b6)
  x₁ x₂ q r i hxu

/-- The corresponding ordinate is at the very same sum depth. -/
def ownSumDepthY : S := sumDepthY W' t (algebraMap R S z.b3) (algebraMap R S z.b6)
  x₁ x₂ q r i L hxu

local notation "X" => ownSumDepthX d e dd ee z a c hc hd hxu i
local notation "Y" => ownSumDepthY d e dd ee z a c hc hd hxu i L
variable (hi : i * (a (x W (π ^ k) d.b3 d.b4 d.b6) -
    algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6)) = 1)
  (hL : L * (a (x W (π ^ k) d.b3 d.b4 d.b6) -
    algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6)) =
      a (y W (π ^ k) d.b3 d.b4 d.b6) -
        algebraMap R S (π ^ (l - k)) * c (y W (π ^ l) e.b3 e.b4 e.b6))

omit [Module.Flat R S] in
include hπ h2 hkl hi hL in
/-- The equation constructs the divided intercept; no ordinate quotient is assumed. -/
theorem ownSumDepth_intercept : y₁ - L * x₁ = s * t * b := by
  apply sumDepthIntercept_scale s t x₁ y₁ x₂ y₂ q r i L hi hL
  · exact ownBranchOrdinate_scale hπ d dd h2 a hc
  · rw [ownSumDepth_rightScale hkl]
    exact ownBranchOrdinate_scale hπ e ee h2 c hd

omit [Module.Flat R S] in
include hπ hkl in
/-- The third input coefficient has the precise factor required by the product identity. -/
theorem ownSumDepth_factor3 : algebraMap R S d.b3 = s * t * algebraMap R S z.b3 := by
  rw [depth_coefficient_factor π k (k + l) hπ (Nat.le_add_right k l)
    d.factor3 z.factor3, Nat.add_sub_cancel_left, map_mul, ownSumDepth_rightScale hkl]

omit [Module.Flat R S] in
include hπ hkl in
/-- The constant input coefficient has the square of the same factor. -/
theorem ownSumDepth_factor6 :
    algebraMap R S d.b6 = (s * t) ^ 2 * algebraMap R S z.b6 := by
  rw [depth_constant_factor π k (k + l) hπ (Nat.le_add_right k l)
    d.factor6 z.factor6, Nat.add_sub_cancel_left, map_mul, map_pow,
    ownSumDepth_rightScale hkl]

include hπ h2 hkl hi hL in
/-- The constructed abscissa scales to the original secant output. -/
theorem ownSumDepthX_scale :
    algebraMap R S (π ^ (k + l)) * X =
      (W').toAffine.addX (s * x₁) (s * (t * x₂)) L := by
  rw [← ownSumDepth_scale hkl]
  apply sumDepthX_scale W' s t (algebraMap R S z.b3) (algebraMap R S z.b6)
    x₁ y₁ x₂ q r i L hxu
  · exact WeierstrassIntegralChart.flatRingHom_isRegular _
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
      (isRegular_iff_ne_zero.mpr (pow_ne_zero _ hπ))
  · exact ownSumDepth_intercept hπ d e hkl dd ee h2 a c hc hd i L hi hL
  · have he := equation_map W (π ^ k) d.b3 d.b4 d.b6
      (unequalDepthRight hπ d e hkl c)
    simp only [unequalDepthRight_x, unequalDepthRight_y] at he
    have hp := divided_secant_product W' s (algebraMap R S d.b3)
      (algebraMap R S d.b4) (algebraMap R S d.b6) x₁ y₁ (t * x₂) (t * y₂) L
      (equation_map W (π ^ k) d.b3 d.b4 d.b6 a) he
      (isUnit_iff_exists_inv.mpr ⟨i, by rwa [mul_comm]⟩) hL
    rwa [ownSumDepth_factor3 hπ d hkl z, ownSumDepth_factor6 hπ d hkl z] at hp

include hπ h2 hkl hi hL in
/-- The constructed ordinate scales to the same original secant output. -/
theorem ownSumDepthY_scale :
    algebraMap R S (π ^ (k + l)) * Y =
      (W').toAffine.addY (s * x₁) (s * (t * x₂)) (s * y₁) L := by
  rw [← ownSumDepth_scale hkl]
  apply sumDepthY_scale W' s t (algebraMap R S z.b3) (algebraMap R S z.b6)
    x₁ y₁ x₂ q r i L hxu
  · rw [WeierstrassCurve.map_a₃, z.factor3, map_mul, ownSumDepth_scale hkl]
  · exact ownSumDepth_intercept hπ d e hkl dd ee h2 a c hc hd i L hi hL
  · rw [ownSumDepth_scale hkl]
    exact ownSumDepthX_scale hπ d e hkl dd ee z h2 a c hc hd hxu i L hi hL

end FLT.Mazur.WeierstrassDividedDepth
