/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFactoredReflectedOutput
public import FLT.Mazur.WeierstrassDividedReflectedBranchResidue
public import FLT.Mazur.WeierstrassDividedVerticalSmooth

/-!
# Reflected residue smoothness without a depth gap

Specialize the constructed coordinates through a field-valued point.
Positive residual depth kills both original ordinates. The invertible secant
difference then kills the slope, even for equal input depths. The exact
constant quotient makes the actual vertical derivative nonzero.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
universe u
variable {R S K : Type u} [CommRing R] [CommRing S] [Field K] [Algebra R K]
  [Algebra R S] [IsDomain R]
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
local notation "q" => factoredCommonBranchOrdinate d
  (reflectedLeftBranchData D d hkl hl) b2 a hc
local notation "r" => factoredCommonBranchOrdinate e
  (reflectedRightBranchData (k := k) D e hl) b2 c hd
local notation "b" => sumDepthIntercept 1 x₁ x₂ q r i
local notation "C" => algebraMap R S (reflectedBranchConstant D d hkl hl)

local notation "X" => nodeFactoredReflectedX D d e hkl hl b2 a c hc hd hxu i
local notation "Y" => nodeFactoredReflectedY D d e hkl hl z b2 a c hc hd hxu i L
variable (hi : i * (a (x W (π ^ k) d.b3 d.b4 d.b6) -
    algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6)) = 1)
  (hL : L * (a (x W (π ^ k) d.b3 d.b4 d.b6) -
    algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6)) =
      a (y W (π ^ k) d.b3 d.b4 d.b6) -
        algebraMap R S (π ^ (l - k)) * c (y W (π ^ l) e.b3 e.b4 e.b6))

variable (ρ : S →ₐ[R] K) (hs : algebraMap R K (π ^ k) = 0)
  (hv : algebraMap R K (π ^ (m - 2 * l)) = 0)
  (he3 : algebraMap R K e.b3 = 0) (hz3 : algebraMap R K z.b3 = 0)

omit [Module.Flat R S] in
include D hkl hl hm h2 hv hc hd hi hL in
/-- The actual chord slope vanishes when the common ordinate scale vanishes. -/
theorem nodeFactoredReflected_secant_residue_slope : ρ L = 0 := by
  have hy := congrArg ρ (factoredCommonBranchOrdinate_scale d
    (reflectedLeftBranchData D d hkl hl) b2 a hc (by omega) h2)
  simp only [map_mul, AlgHom.commutes, hv, zero_mul] at hy
  have hy₂ := congrArg ρ (factoredCommonBranchOrdinate_scale e
    (reflectedRightBranchData (k := k) D e hl) b2 c hd (by omega) h2)
  simp only [map_mul, AlgHom.commutes, hv, zero_mul] at hy₂
  have hinv := congrArg ρ hi
  have hline := congrArg ρ hL
  rw [map_mul, map_one] at hinv
  have hyz : ρ (y₁ - t * y₂) = 0 := by
    simp only [map_sub, map_mul, ← hy, ← hy₂, mul_zero, sub_self]
  rw [map_mul, hyz] at hline
  have hx : ρ (x₁ - t * x₂) ≠ 0 := by
    intro hx
    rw [hx, mul_zero] at hinv
    exact zero_ne_one hinv
  exact (mul_eq_zero.mp hline).resolve_right hx

include hm h2 hs hv he3 hz3 hi hL in
/-- The full output map has nonzero vertical derivative on specialization. -/
theorem nodeFactoredReflectedOutput_secant_residue_vertical (ha : algebraMap R K W.a₁ ≠ 0) :
    ρ (nodeFactoredReflectedOutput D d e hkl hl hm z b2 h2 a c hc hd hxu i L hi hL
      (verticalDerivative W (π ^ (m - k - l)) z.b3 z.b4 z.b6)) ≠ 0 := by
  have hu : IsUnit (ρ x₁ * ρ x₂) := by simpa only [map_mul] using hxu.map ρ
  have hC := ((reflectedBranchConstant_isUnit D d hkl hl).map (algebraMap R K)).ne_zero
  have hLi := nodeFactoredReflected_secant_residue_slope D d e hkl hl hm b2 h2
    a c hc hd i L hi hL ρ hv
  have huinv : ρ (↑hxu.unit⁻¹ : S) = (↑hu.unit⁻¹ : K) := by
    simpa only [map_mul] using (hxu.unit_inv_map ρ).symm
  have hX : ρ X = reflectedBranchX 0 0 (algebraMap R K
      (reflectedBranchConstant D d hkl hl)) (ρ x₁) (ρ x₂) (ρ q) (ρ r) (ρ i) hu := by
    simp only [map_pow] at hv
    simp only [nodeFactoredReflectedX, reflectedBranchX, sumDepthIntercept, map_mul, map_sub,
      map_add, map_pow, map_one, AlgHom.commutes, hv, he3, huinv]
  have hY : ρ Y = reflectedBranchY (W.map (algebraMap R K)) 0 0 0
      (algebraMap R K (reflectedBranchConstant D d hkl hl)) 0
      (ρ x₁) (ρ x₂) (ρ q) (ρ r) (ρ i) 0 hu := by
    change ρ (-(L + algebraMap R S W.a₁) * X - s * b - algebraMap R S z.b3) = _
    simp only [reflectedBranchY, sumDepthIntercept, map_mul, map_sub, map_add, map_neg,
      map_one, AlgHom.commutes, hs, hz3, hLi, hX, WeierstrassCurve.map_a₁,
      zero_mul, sub_zero]
  have hn := reflectedBranch_residue_vertical (W.map (algebraMap R K))
    (algebraMap R K (reflectedBranchConstant D d hkl hl))
    (ρ x₁) (ρ x₂) (ρ q) (ρ r) (ρ i) hu ha hC
  simpa only [verticalDerivative_eq, map_add, map_mul, map_ofNat, AlgHom.commutes,
    nodeFactoredReflectedOutput_x, nodeFactoredReflectedOutput_y, hz3, add_zero, hX, hY,
    WeierstrassCurve.map_a₁] using hn

end FLT.Mazur.WeierstrassDividedDepth
