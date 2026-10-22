/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFactoredSumOutput
public import FLT.Mazur.WeierstrassDividedFactoredCommonBranchResidue
public import FLT.Mazur.WeierstrassDividedFactoredSumResidueFormula
public import FLT.Mazur.WeierstrassDividedVerticalSmooth

/-!
# Smooth sum-depth residues retaining the quadratic quotient

The quadratic contributions to the two branch ordinates cancel in the
intercept. The actual output therefore has a nonzero vertical derivative,
without setting the finite quadratic quotient to zero.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
universe u
variable {R S K : Type u} [CommRing R] [CommRing S] [Field K] [Algebra R K]
  [Algebra R S] [IsDomain R]
  [Module.Flat R S] {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k l : ℕ}
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (dd : CommonBranchData d k) (ee : CommonBranchData e k) (z : Data W π (k + l))
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
local notation "q" => factoredCommonBranchOrdinate d dd b2 a hc
local notation "r" => factoredCommonBranchOrdinate e ee b2 c hd
local notation "b" => sumDepthIntercept 1 x₁ x₂ q r i

variable (hi : i * (a (x W (π ^ k) d.b3 d.b4 d.b6) -
    algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6)) = 1)
  (hL : L * (a (x W (π ^ k) d.b3 d.b4 d.b6) -
    algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6)) =
      a (y W (π ^ k) d.b3 d.b4 d.b6) -
        algebraMap R S (π ^ (l - k)) * c (y W (π ^ l) e.b3 e.b4 e.b6))

local notation "X" => factoredSumDepthX d e dd ee z b2 a c hc hd hxu i
local notation "Y" => factoredSumDepthY d e dd ee z b2 a c hc hd hxu i L

variable (ρ : S →ₐ[R] K) (hs : algebraMap R K (π ^ k) = 0)
  (ht : algebraMap R K (π ^ (l - k)) = 0) (h3 : algebraMap R K d.b3 = 0)
  (h4 : algebraMap R K dd.b4 = 0) (h6 : algebraMap R K dd.b6 = 0) (hz3 : algebraMap R K z.b3 = 0)
  (hz6 : algebraMap R K z.b6 = 0)
  (he3 : algebraMap R K e.b3 = 0) (he4 : algebraMap R K ee.b4 = 0) (he6 : algebraMap R K ee.b6 = 0)
local notation "α" => algebraMap R K W.a₁

include hπ h2 hs ht h3 h4 h6 hz3 hz6 he3 he4 he6 hi hL in
/-- The actual sum-depth output is vertically smooth after specialization. -/
theorem factoredSumDepthOutput_residue_vertical (ha : α ≠ 0) :
    ρ (factoredSumDepthOutput hπ d e hkl dd ee z b2 h2 a c hc hd hxu i L hi hL
      (verticalDerivative W (π ^ (k + l)) z.b3 z.b4 z.b6)) ≠ 0 := by
  have hu : IsUnit (ρ x₁ * ρ x₂) := by simpa only [map_mul] using hxu.map ρ
  have hx : ρ x₁ ≠ 0 := (mul_ne_zero_iff.mp hu.ne_zero).1
  have hu₂ : ρ x₂ ≠ 0 := (mul_ne_zero_iff.mp hu.ne_zero).2
  have hy₁ := factoredCommonBranchOrdinate_residue_ordinate d dd b2 a hc ρ le_rfl h2 hs
  have hy₂ := factoredCommonBranchOrdinate_residue_ordinate e ee b2 c hd ρ hkl h2 hs
  have hq := factoredCommonBranchOrdinate_residue_leading d dd b2 a hc ρ 1
    (by simp only [Nat.sub_self, pow_zero, map_one]) hy₁ h3 h4 h6 hx
  have hr := factoredCommonBranchOrdinate_residue_leading e ee b2 c hd ρ 0
    ht hy₂ he3 he4 he6 hu₂
  simp only [one_mul] at hq
  simp only [zero_mul, zero_add] at hr
  have hinv := congrArg ρ hi
  simp only [map_mul, map_sub, map_one, AlgHom.commutes, ht, zero_mul, sub_zero] at hinv
  have hl : ρ L = 0 := by
    have h := congrArg ρ hL
    simp only [map_mul, map_sub, AlgHom.commutes, ht, hy₁, zero_mul, sub_zero] at h
    exact (mul_eq_zero.mp h).resolve_right hx
  have huinv : ρ (↑hxu.unit⁻¹ : S) = (↑hu.unit⁻¹ : K) := by
    simpa only [map_mul] using (hxu.unit_inv_map ρ).symm
  have hX : ρ X = sumDepthX 1 0 0 (ρ x₁) (ρ x₂) (ρ q) (ρ r) (ρ i) hu := by
    simp only [factoredSumDepthX, sumDepthX, sumDepthIntercept, map_mul, map_sub, map_add,
      map_pow, map_one, AlgHom.commutes, hz3, hz6, huinv, zero_mul,
      sub_zero]
  have hY : ρ Y = sumDepthY (W.map (algebraMap R K)) 1 0 0
      (ρ x₁) (ρ x₂) (ρ q) (ρ r) (ρ i) 0 hu := by
    change ρ (-(L + algebraMap R S W.a₁) * X - b - algebraMap R S z.b3) = _
    simp only [sumDepthY, sumDepthIntercept, map_mul, map_sub, map_add, map_neg,
      map_one, AlgHom.commutes, hz3, hl, hX, WeierstrassCurve.map_a₁,
      sub_zero]
  have hn := factoredSumDepth_residue_vertical (W.map (algebraMap R K))
    (algebraMap R K b2) (ρ x₁) (ρ x₂) (ρ q) (ρ r) (ρ i) hu ha hinv hq hr
  simpa only [verticalDerivative_eq, map_add, map_mul, map_ofNat, AlgHom.commutes,
    factoredSumDepthOutput_x, factoredSumDepthOutput_y, hz3, add_zero, hX, hY,
    WeierstrassCurve.map_a₁] using hn

end FLT.Mazur.WeierstrassDividedDepth
