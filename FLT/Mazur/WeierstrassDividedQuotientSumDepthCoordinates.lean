/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedQuotientBranchOrdinate
public import FLT.Mazur.WeierstrassDividedOwnSumDepthCoordinates
public import FLT.Mazur.WeierstrassDividedSumDepthFormula
public import FLT.Mazur.WeierstrassDividedUnequalDepthSecant

/-!
# Sum-depth coordinates with weaker branch coefficients

Construct the same sum-depth coordinates using only coefficient quotients
at each input. Triple-depth bounds will supply these quotients.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [Module.Flat R S] {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k l : ℕ}
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (dd : BranchQuotientData d) (ee : BranchQuotientData e) (z : Data W π (k + l))
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
local notation "q" => quotientBranchOrdinate d dd a hc
local notation "r" => quotientBranchOrdinate e ee c hd
local notation "b" => sumDepthIntercept t x₁ x₂ q r i

/-- The abscissa is constructed from the two actual branch-ordinate quotients. -/
def quotientSumDepthX : S := sumDepthX t (algebraMap R S z.b3) (algebraMap R S z.b6)
  x₁ x₂ q r i hxu

/-- The corresponding ordinate is at the very same sum depth. -/
def quotientSumDepthY : S := sumDepthY W' t (algebraMap R S z.b3) (algebraMap R S z.b6)
  x₁ x₂ q r i L hxu

local notation "X" => quotientSumDepthX d e dd ee z a c hc hd hxu i
local notation "Y" => quotientSumDepthY d e dd ee z a c hc hd hxu i L
variable (hi : i * (a (x W (π ^ k) d.b3 d.b4 d.b6) -
    algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6)) = 1)
  (hL : L * (a (x W (π ^ k) d.b3 d.b4 d.b6) -
    algebraMap R S (π ^ (l - k)) * c (x W (π ^ l) e.b3 e.b4 e.b6)) =
      a (y W (π ^ k) d.b3 d.b4 d.b6) -
        algebraMap R S (π ^ (l - k)) * c (y W (π ^ l) e.b3 e.b4 e.b6))

omit [IsDomain R] [Module.Flat R S] in
include h2 hkl hi hL in
/-- The equation constructs the divided intercept; no ordinate quotient is assumed. -/
theorem quotientSumDepth_intercept : y₁ - L * x₁ = s * t * b := by
  apply sumDepthIntercept_scale s t x₁ y₁ x₂ y₂ q r i L hi hL
  · exact quotientBranchOrdinate_scale d dd h2 a hc
  · rw [ownSumDepth_rightScale hkl]
    exact quotientBranchOrdinate_scale e ee h2 c hd

include hπ h2 hkl hi hL in
/-- The constructed abscissa scales to the original secant output. -/
theorem quotientSumDepthX_scale :
    algebraMap R S (π ^ (k + l)) * X =
      (W').toAffine.addX (s * x₁) (s * (t * x₂)) L := by
  rw [← ownSumDepth_scale hkl]
  apply sumDepthX_scale W' s t (algebraMap R S z.b3) (algebraMap R S z.b6)
    x₁ y₁ x₂ q r i L hxu
  · exact WeierstrassIntegralChart.flatRingHom_isRegular _
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
      (isRegular_iff_ne_zero.mpr (pow_ne_zero _ hπ))
  · exact quotientSumDepth_intercept d e hkl dd ee h2 a c hc hd i L hi hL
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
theorem quotientSumDepthY_scale :
    algebraMap R S (π ^ (k + l)) * Y =
      (W').toAffine.addY (s * x₁) (s * (t * x₂)) (s * y₁) L := by
  rw [← ownSumDepth_scale hkl]
  apply sumDepthY_scale W' s t (algebraMap R S z.b3) (algebraMap R S z.b6)
    x₁ y₁ x₂ q r i L hxu
  · rw [WeierstrassCurve.map_a₃, z.factor3, map_mul, ownSumDepth_scale hkl]
  · exact quotientSumDepth_intercept d e hkl dd ee h2 a c hc hd i L hi hL
  · rw [ownSumDepth_scale hkl]
    exact quotientSumDepthX_scale hπ d e hkl dd ee z h2 a c hc hd hxu i L hi hL

end FLT.Mazur.WeierstrassDividedDepth
