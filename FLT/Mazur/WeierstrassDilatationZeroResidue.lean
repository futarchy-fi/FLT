/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationGenericFiber
public import FLT.Mazur.WeierstrassDilatationResidueRetained
public import FLT.Mazur.WeierstrassSplitDepthResidueEquation

/-!
# The entire divided residue chart at depth zero

At depth zero the scale remains one. The full tensor chart is the original
split nodal affine cubic, retaining both original coordinates. The
positive-depth tangent-product normal form does not describe this case.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hdepth : 0 < depth) (k : ℕ) (hk : k = 0) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6)
local notation "K" => ResidueField R
local notation "W₀" => W.map (algebraMap R K)
local notation "s" => algebraMap R K (π ^ k)
local notation "c3" => algebraMap R K b3
local notation "c4" => algebraMap R K b4
local notation "c6" => algebraMap R K b6
omit [IsDomain R] in
include hk in
/-- At depth zero the residue scale is a unit because it is one. -/
theorem zeroResidue_scale_isUnit : IsUnit s := by
  simp only [hk, pow_zero, map_one]
  exact isUnit_one

local notation "hs" => zeroResidue_scale_isUnit (π := π) k hk
local notation "g" => specializedOriginalEquiv W (π ^ k) b3 b4 b6 h3 h4 h6 K hs

/-- The zero-depth specialized chart retains the original affine cubic exactly. -/
def zeroResidueAffineEquiv : ScalarExtension W (π ^ k) b3 b4 b6 K ≃ₐ[K]
    WeierstrassIntegralChart.Coordinate W₀ 2 :=
  (baseChangeEquiv W (π ^ k) b3 b4 b6 K).trans (g).symm

omit [IsDomain R] in
/-- The horizontal coordinate is unchanged at depth zero. -/
theorem zeroResidueAffineEquiv_x :
    zeroResidueAffineEquiv k hk b3 b4 b6 h3 h4 h6
      (tensorX W (π ^ k) b3 b4 b6 K) = WeierstrassIntegralChart.coord W₀ 2 0 := by
  change (g).symm (baseChangeEquiv W (π ^ k) b3 b4 b6 K
    (tensorX W (π ^ k) b3 b4 b6 K)) = _
  apply (g).symm_apply_eq.mpr
  rw [baseChangeEquiv_tensorX, specializedOriginalEquiv_x]
  simp only [hk, pow_zero, map_one, one_mul]

omit [IsDomain R] in
/-- The vertical coordinate is unchanged at depth zero. -/
theorem zeroResidueAffineEquiv_y :
    zeroResidueAffineEquiv k hk b3 b4 b6 h3 h4 h6
      (tensorY W (π ^ k) b3 b4 b6 K) = WeierstrassIntegralChart.coord W₀ 2 1 := by
  change (g).symm (baseChangeEquiv W (π ^ k) b3 b4 b6 K
    (tensorY W (π ^ k) b3 b4 b6 K)) = _
  apply (g).symm_apply_eq.mpr
  rw [baseChangeEquiv_tensorY, specializedOriginalEquiv_y]
  simp only [hk, pow_zero, map_one, one_mul]

/-- The whole zero-depth tensor chart is the actual nodal affine cubic. -/
def zeroResidueNodalEquiv : ScalarExtension W (π ^ k) b3 b4 b6 K ≃ₐ[K]
    WeierstrassIntegralChart.Coordinate
      (WeierstrassIntegralChart.splitNodalEquation (residueTangentUnit D)) 2 :=
  (zeroResidueAffineEquiv k hk b3 b4 b6 h3 h4 h6).trans
    (WeierstrassIntegralChart.equationChartEquiv
      (WeierstrassIntegralChart.splitDepth_residue_equation D hdepth) 2)

/-- The full nodal comparison keeps the original horizontal tensor function. -/
theorem zeroResidueNodalEquiv_x :
    zeroResidueNodalEquiv D hdepth k hk b3 b4 b6 h3 h4 h6
      (tensorX W (π ^ k) b3 b4 b6 K) = WeierstrassIntegralChart.coord
        (WeierstrassIntegralChart.splitNodalEquation (residueTangentUnit D)) 2 0 := by
  rw [zeroResidueNodalEquiv, AlgEquiv.trans_apply, zeroResidueAffineEquiv_x,
    WeierstrassIntegralChart.equationChartEquiv_coord]

/-- The full nodal comparison keeps the original vertical tensor function. -/
theorem zeroResidueNodalEquiv_y :
    zeroResidueNodalEquiv D hdepth k hk b3 b4 b6 h3 h4 h6
      (tensorY W (π ^ k) b3 b4 b6 K) = WeierstrassIntegralChart.coord
        (WeierstrassIntegralChart.splitNodalEquation (residueTangentUnit D)) 2 1 := by
  rw [zeroResidueNodalEquiv, AlgEquiv.trans_apply, zeroResidueAffineEquiv_y,
    WeierstrassIntegralChart.equationChartEquiv_coord]

end FLT.Mazur.WeierstrassDilatation
