/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReflectedBranchOutput
public import FLT.Mazur.WeierstrassDividedReflectedTerminalResidue
public import FLT.Mazur.WeierstrassDividedReflectedConstantCompare
public import FLT.Mazur.WeierstrassDividedVerticalSmooth

/-!
# Actual reflected output smoothness at even terminal input depth

Transport the surviving square calculation through the original output map.
The terminal ordinate remains unrestricted; its nonzero constant coefficient
forces the nonvanishing needed for the output derivative.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
universe u
variable {R S K : Type u} [CommRing R] [CommRing S] [Field K]
  [Algebra R K] [Algebra R S] [IsDomain R]
  [IsLocalRing R] [Module.Flat R S] {W : WeierstrassCurve R} {π : R} {k l m : ℕ}
  (D : SplitNodeDepth W π m) (d : Data W π k) (e : Data W π l)
  (hkl : k ≤ l) (hl : 2 * l ≤ m) (hm : m ≤ k + 2 * l)
  (z : Data W π (m - k - l)) (h2 : W.a₂ = 0)
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
local notation "q" => commonBranchOrdinate d (reflectedLeftBranchData D d hkl hl) a hc
local notation "r" => commonBranchOrdinate e (reflectedRightBranchData (k := k) D e hl) c hd
local notation "b" => sumDepthIntercept 1 x₁ x₂ q r i
local notation "C" => algebraMap R S (reflectedBranchConstant D d hkl hl)

local notation "X" => nodeReflectedX D d e hkl hl a c hc hd hxu i
local notation "Y" => nodeReflectedY D d e hkl hl z a c hc hd hxu i L
variable (hi : i * (a (x W (π ^ k) d.b3 d.b4 d.b6) -
    algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6)) = 1)
  (hL : L * (a (x W (π ^ k) d.b3 d.b4 d.b6) -
    algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6)) =
      a (y W (π ^ k) d.b3 d.b4 d.b6) -
        algebraMap R S (π ^ (l - k)) * c (y W (π ^ l) e.b3 e.b4 e.b6))

variable (ρ : S →ₐ[R] K)

/-- The actual terminal output has nonzero vertical derivative without killing its square. -/
theorem nodeReflectedOutput_terminal_vertical (hm0 : m = 2 * l)
    (hs : algebraMap R K (π ^ k) = 0) (ht : algebraMap R K (π ^ (l - k)) = 0)
    (hl0 : algebraMap R K (π ^ l) = 0)
    (he3 : algebraMap R K e.b3 = 0) (he4 : algebraMap R K e.b4 = 0)
    (hz3 : algebraMap R K z.b3 = 0) (hy : ρ y₁ = 0)
    (ha : algebraMap R K W.a₁ ≠ 0) :
    ρ (nodeReflectedOutput D d e hkl hl hm z h2 a c hc hd hxu i L hi hL
      (verticalDerivative W (π ^ (m - k - l)) z.b3 z.b4 z.b6)) ≠ 0 := by
  have hu : IsUnit (ρ x₁ * ρ x₂) := by simpa only [map_mul] using hxu.map ρ
  have hC := reflectedBranchConstant_terminal D d e hkl hl hm0
  have hC0 : algebraMap R K e.b6 ≠ 0 := by
    rw [← hC]
    exact ((reflectedBranchConstant_isUnit D d hkl hl).map (algebraMap R K)).ne_zero
  have hq : ρ q = 0 := by
    have h := congrArg ρ (commonBranchOrdinate_scale d
      (reflectedLeftBranchData D d hkl hl) a hc (by omega) h2)
    simpa only [hm0, Nat.sub_self, pow_zero, map_one, one_mul, hy] using h
  have hr : ρ r = ρ y₂ := by
    have h := congrArg ρ (commonBranchOrdinate_scale e
      (reflectedRightBranchData (k := k) D e hl) c hd (by omega) h2)
    simpa only [hm0, Nat.sub_self, pow_zero, map_one, one_mul] using h
  have hinv := congrArg ρ hi
  simp only [map_mul, map_sub, map_one, AlgHom.commutes, ht, zero_mul, sub_zero] at hinv
  have hLi : ρ L = 0 := by
    have hline := congrArg ρ hL
    simp only [map_mul, map_sub, AlgHom.commutes, ht, hy, zero_mul, sub_zero] at hline
    exact (mul_eq_zero.mp hline).resolve_right (mul_ne_zero_iff.mp hu.ne_zero).1
  have heq : (ρ y₂) ^ 2 + algebraMap R K W.a₁ * ρ x₂ * ρ y₂ =
      algebraMap R K e.b6 := by
    have h := equation_map W (π ^ l) e.b3 e.b4 e.b6 (ρ.comp c)
    simpa only [AlgHom.comp_apply, hl0, he3, he4, h2, map_zero, zero_mul,
      zero_add, add_zero] using h
  have huinv : ρ (↑hxu.unit⁻¹ : S) = (↑hu.unit⁻¹ : K) := by
    simpa only [map_mul] using (hxu.unit_inv_map ρ).symm
  have hX : ρ X = reflectedBranchX 1 0 (algebraMap R K e.b6)
      (ρ x₁) (ρ x₂) 0 (ρ y₂) (ρ i) hu := by
    simp only [nodeReflectedX, hC]
    simp only [reflectedBranchX, sumDepthIntercept, map_mul, map_sub,
      map_add, map_pow, map_one, AlgHom.commutes, hm0, Nat.sub_self, pow_zero,
      he3, hq, hr, huinv]
  have hY : ρ Y = reflectedBranchY (W.map (algebraMap R K)) 0 1 0
      (algebraMap R K e.b6) 0 (ρ x₁) (ρ x₂) 0 (ρ y₂) (ρ i) 0 hu := by
    change ρ (-(L + algebraMap R S W.a₁) * X - s * b - algebraMap R S z.b3) = _
    simp only [reflectedBranchY, sumDepthIntercept, map_mul, map_sub, map_add, map_neg,
      map_one, AlgHom.commutes, hs, hz3, hLi, hX, WeierstrassCurve.map_a₁,
      zero_mul, sub_zero]
  have hn := reflectedTerminal_vertical (W.map (algebraMap R K))
    (algebraMap R K e.b6) (ρ x₁) (ρ x₂) (ρ y₂) (ρ i) hu ha hC0 hinv heq
  simpa only [verticalDerivative_eq, map_add, map_mul, map_ofNat, AlgHom.commutes,
    nodeReflectedOutput_x, nodeReflectedOutput_y, hz3, add_zero, hX, hY,
    WeierstrassCurve.map_a₁] using hn

end FLT.Mazur.WeierstrassDividedDepth
