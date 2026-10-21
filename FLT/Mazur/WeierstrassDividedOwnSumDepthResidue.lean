/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOwnSumDepthOutput
public import FLT.Mazur.WeierstrassDividedOwnBranchResidue
public import FLT.Mazur.WeierstrassDividedSumDepthResidue
public import FLT.Mazur.WeierstrassDividedVerticalSmooth

/-!
# Residues of the actual sum-depth output

Transport the constructed branch ordinates and inverse through a field-valued
point. The output derivative is nonzero under explicit coefficient vanishings;
no output smoothness or output coordinates are assumed.
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

variable (hi : i * (a (x W (π ^ k) d.b3 d.b4 d.b6) -
    algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6)) = 1)
  (hL : L * (a (x W (π ^ k) d.b3 d.b4 d.b6) -
    algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6)) =
      a (y W (π ^ k) d.b3 d.b4 d.b6) -
        algebraMap R S (π ^ (l - k)) * c (y W (π ^ l) e.b3 e.b4 e.b6))

local notation "X" => ownSumDepthX d e dd ee z a c hc hd hxu i
local notation "Y" => ownSumDepthY d e dd ee z a c hc hd hxu i L

variable (ρ : S →ₐ[R] K) (hs : algebraMap R K (π ^ k) = 0)
  (ht : algebraMap R K (π ^ (l - k)) = 0) (h3 : algebraMap R K d.b3 = 0)
  (h4 : algebraMap R K dd.b4 = 0) (hz3 : algebraMap R K z.b3 = 0)
  (hz6 : algebraMap R K z.b6 = 0)
local notation "α" => algebraMap R K W.a₁
local notation "b₀" => sumDepthIntercept 0 (ρ x₁) (ρ x₂) (ρ q) (ρ r) (ρ i)

omit [Module.Flat R S] in
include hπ h2 hs ht hi hL dd hc in
/-- The constructed secant slope vanishes on these positive closed-fiber inputs. -/
theorem ownSumDepth_residue_slope : ρ L = 0 := by
  have hy := ownBranchOrdinate_residue_y hπ d dd h2 a hc ρ hs
  have hinv := congrArg ρ hi
  have hl := congrArg ρ hL
  simp only [map_mul, map_sub, map_one, AlgHom.commutes, ht, zero_mul, sub_zero] at hinv
  simp only [map_mul, map_sub, AlgHom.commutes, ht, hy, zero_mul, sub_zero] at hl
  have hx : ρ x₁ ≠ 0 := by
    intro hx
    rw [hx, mul_zero] at hinv
    exact zero_ne_one hinv
  exact (mul_eq_zero.mp hl).resolve_right hx

include hπ h2 hs ht h3 h4 hz3 hz6 hi hL in
/-- The actual sum-depth output is vertically smooth after specialization. -/
theorem ownSumDepthOutput_residue_vertical (ha : α ≠ 0) :
    ρ (ownSumDepthOutput hπ d e hkl dd ee z h2 a c hc hd hxu i L hi hL
      (verticalDerivative W (π ^ (k + l)) z.b3 z.b4 z.b6)) ≠ 0 := by
  have hu : IsUnit (ρ x₁ * ρ x₂) := by simpa only [map_mul] using hxu.map ρ
  have hx : ρ x₁ ≠ 0 := (mul_ne_zero_iff.mp hu.ne_zero).1
  have hq := ownBranchOrdinate_residue_leading hπ d dd h2 a hc ρ hs h3 h4 hx
  have hinv := congrArg ρ hi
  simp only [map_mul, map_sub, map_one, AlgHom.commutes, ht, zero_mul, sub_zero] at hinv
  have hl := ownSumDepth_residue_slope hπ d e dd h2 a c hc i L hi hL ρ hs ht
  have huinv : ρ (↑hxu.unit⁻¹ : S) = (↑hu.unit⁻¹ : K) := by
    simpa only [map_mul] using (hxu.unit_inv_map ρ).symm
  have hX : ρ X = sumDepthX 0 0 0 (ρ x₁) (ρ x₂) (ρ q) (ρ r) (ρ i) hu := by
    simp only [map_pow] at ht
    simp only [ownSumDepthX, sumDepthX, sumDepthIntercept, map_mul, map_sub, map_add,
      map_pow, AlgHom.commutes, ht, hz3, hz6, huinv]
  have hY : ρ Y = sumDepthY (W.map (algebraMap R K)) 0 0 0
      (ρ x₁) (ρ x₂) (ρ q) (ρ r) (ρ i) 0 hu := by
    change ρ (-(L + algebraMap R S W.a₁) * X - b - algebraMap R S z.b3) = _
    simp only [map_pow] at ht
    simp only [sumDepthY, sumDepthIntercept, map_mul, map_sub, map_add, map_neg,
      map_pow, AlgHom.commutes, ht, hz3, hl, hX, WeierstrassCurve.map_a₁]
  have hn := sumDepth_residue_vertical (W.map (algebraMap R K))
    (ρ x₁) (ρ x₂) (ρ q) (ρ r) (ρ i) hu ha hinv hq
  simpa only [verticalDerivative_eq, map_add, map_mul, map_ofNat, AlgHom.commutes,
    ownSumDepthOutput_x, ownSumDepthOutput_y, hz3, add_zero, hX, hY,
    WeierstrassCurve.map_a₁] using hn

end FLT.Mazur.WeierstrassDividedDepth
