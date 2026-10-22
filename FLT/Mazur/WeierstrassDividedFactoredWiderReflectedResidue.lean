/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFactoredWiderReflectedOutput
public import FLT.Mazur.WeierstrassDividedReflectedBranchResidue
public import FLT.Mazur.WeierstrassDividedVerticalSmooth

/-!
# Residue smoothness with a finite quadratic coefficient quotient

Specialize the constructed coordinates through a field-valued point.
Positive numerator depth kills the wider scale; the exact
constant quotient then makes the actual vertical derivative nonzero.
Both branch ordinates retain the quadratic coefficient quotient.
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
  (hkl : k ≤ l) (hm : k + 2 * l ≤ m) (htop : m ≤ 2 * (k + l))
  (z : Data W π (m - k - l)) (b2 : R) (h2 : W.a₂ = π ^ k * b2)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "s" => algebraMap R S (π ^ k)
local notation "t" => algebraMap R S (π ^ (l - k))
local notation "v" => algebraMap R S (π ^ (2 * (k + l) - m))
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
  (commonBranchData (k := k) D d (by omega : k + 2 * k ≤ m)) b2 a hc
local notation "r" => factoredCommonBranchOrdinate e (commonBranchData D e hm) b2 c hd
local notation "b" => sumDepthIntercept 1 x₁ x₂ q r i
local notation "C" => algebraMap R S (reflectedBranchConstant D d hkl (by omega : 2 * l ≤ m))

local notation "X" => nodeFactoredWiderReflectedX D d e hkl hm z b2 a c hc hd hxu i
local notation "Y" => nodeFactoredWiderReflectedY D d e hkl hm z b2 a c hc hd hxu i L
variable (hi : i * (a (x W (π ^ k) d.b3 d.b4 d.b6) -
    algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6)) = 1)
  (hL : L * (a (x W (π ^ k) d.b3 d.b4 d.b6) -
    algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6)) =
      a (y W (π ^ k) d.b3 d.b4 d.b6) -
        algebraMap R S (π ^ (l - k)) * c (y W (π ^ l) e.b3 e.b4 e.b6))

variable (ρ : S →ₐ[R] K) (hs : algebraMap R K (π ^ k) = 0)
  (ht : algebraMap R K (π ^ (l - k)) = 0)
  (hv : algebraMap R K (π ^ (2 * (k + l) - m)) = 0)
  (hz3 : algebraMap R K z.b3 = 0)

omit [Module.Flat R S] in
include D hkl hm h2 hs ht hc hi hL in
/-- The actual chord slope vanishes when the common ordinate scale vanishes. -/
theorem nodeFactoredWiderReflected_residue_slope : ρ L = 0 := by
  have hy := congrArg ρ (factoredCommonBranchOrdinate_scale d
    (commonBranchData (k := k) D d (by omega)) b2 a hc le_rfl h2)
  simp only [map_mul, AlgHom.commutes, hs, zero_mul] at hy
  have hinv := congrArg ρ hi
  have hline := congrArg ρ hL
  simp only [map_mul, map_sub, map_one, AlgHom.commutes, ht, zero_mul, sub_zero] at hinv
  simp only [map_mul, map_sub, AlgHom.commutes, ht, ← hy, zero_mul, sub_zero] at hline
  have hx : ρ x₁ ≠ 0 := by
    intro hx
    rw [hx, mul_zero] at hinv
    exact zero_ne_one hinv
  exact (mul_eq_zero.mp hline).resolve_right hx

include htop h2 hs ht hv hz3 hi hL in
/-- The full output map has nonzero vertical derivative on specialization. -/
theorem nodeFactoredWiderReflectedOutput_residue_vertical (ha : algebraMap R K W.a₁ ≠ 0) :
    ρ (nodeFactoredWiderReflectedOutput D d e hkl hm htop z b2 h2 a c hc hd hxu i L hi hL
      (verticalDerivative W (π ^ (m - k - l)) z.b3 z.b4 z.b6)) ≠ 0 := by
  have hu : IsUnit (ρ x₁ * ρ x₂) := by simpa only [map_mul] using hxu.map ρ
  have hC := ((reflectedBranchConstant_isUnit D d hkl
    (by omega : 2 * l ≤ m)).map (algebraMap R K)).ne_zero
  have hLi := nodeFactoredWiderReflected_residue_slope D d e hkl hm b2 h2 a c hc i L hi hL ρ hs ht
  have huinv : ρ (↑hxu.unit⁻¹ : S) = (↑hu.unit⁻¹ : K) := by
    simpa only [map_mul] using (hxu.unit_inv_map ρ).symm
  have hX : ρ X = reflectedBranchX 0 0 (algebraMap R K
      (reflectedBranchConstant D d hkl (by omega : 2 * l ≤ m)))
      (ρ x₁) (ρ x₂) (ρ q) (ρ r) (ρ i) hu := by
    simp only [map_pow] at hv
    simp only [nodeFactoredWiderReflectedX, reflectedBranchX, sumDepthIntercept, map_mul, map_sub,
      map_add, map_pow, map_one, AlgHom.commutes, hv, hz3, huinv]
  have hY : ρ Y = reflectedBranchY (W.map (algebraMap R K)) 0 0 0
      (algebraMap R K (reflectedBranchConstant D d hkl (by omega : 2 * l ≤ m))) 0
      (ρ x₁) (ρ x₂) (ρ q) (ρ r) (ρ i) 0 hu := by
    change ρ (-(L + algebraMap R S W.a₁) * X - v * b - algebraMap R S z.b3) = _
    simp only [reflectedBranchY, sumDepthIntercept, map_mul, map_sub, map_add, map_neg,
      map_one, AlgHom.commutes, hv, hz3, hLi, hX, WeierstrassCurve.map_a₁,
      zero_mul, sub_zero]
  have hn := reflectedBranch_residue_vertical (W.map (algebraMap R K))
    (algebraMap R K (reflectedBranchConstant D d hkl (by omega : 2 * l ≤ m)))
    (ρ x₁) (ρ x₂) (ρ q) (ρ r) (ρ i) hu ha hC
  simpa only [verticalDerivative_eq, map_add, map_mul, map_ofNat, AlgHom.commutes,
    nodeFactoredWiderReflectedOutput_x, nodeFactoredWiderReflectedOutput_y, hz3, add_zero, hX, hY,
    WeierstrassCurve.map_a₁] using hn

end FLT.Mazur.WeierstrassDividedDepth
