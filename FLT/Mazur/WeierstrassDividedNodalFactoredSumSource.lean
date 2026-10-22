/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFactoredSumOutput
public import FLT.Mazur.WeierstrassDividedNodalSecondNormalization
public import FLT.Mazur.WeierstrassDividedShearBranchSource
public import FLT.Mazur.WeierstrassDividedSumDepthSourceOutput

/-!
# Normalized sum-depth outputs with no zero quadratic coefficient assumption

Normalize through the shallower input depth, construct both factored branch
ordinates, and return the actual sum through the inverse shear. Both output
coordinates contract to the original unsheared secant.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [IsDomain R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k l m : ℕ}
  (D : SplitNodeDepth W π m) (d : Data W π k) (e : Data W π l)
  (hkl : k ≤ l) (hm : k + 2 * l ≤ m)
  (z : Data W π (k + l))
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "σ" => nodalSecondShear D k
local notation "V" => rootShearCurve W σ
local notation "sd" => (⟨d.b3, d.b4 - σ * d.b3, d.b6,
  (shearData d σ).factor3, (shearData d σ).factor4,
  (shearData d σ).factor6⟩ : Data V π k)
local notation "se" => (⟨e.b3, e.b4 - σ * e.b3, e.b6,
  (shearData e σ).factor3, (shearData e σ).factor4,
  (shearData e σ).factor6⟩ : Data V π l)
local notation "sz" => (⟨z.b3, z.b4 - σ * z.b3, z.b6,
  (shearData z σ).factor3, (shearData z σ).factor4,
  (shearData z σ).factor6⟩ : Data V π (k + l))
local notation "N" => nodalSecondShear_depth D k
local notation "b2" => nodalSecondQuotient D k
local notation "h2" => nodalSecondQuotient_factor D k
local notation "a'" => branchShearInput W (π ^ k) d.b3 d.b4 d.b6 σ a
local notation "c'" => branchShearInput W (π ^ l) e.b3 e.b4 e.b6 σ c
local notation "B" => SumDepthSourceRing sd se a' c'
local notation "j" => IsScalarTower.toAlgHom R S B
local notation "aa" => (j).comp a'
local notation "cc" => (j).comp c'
local notation "hc" => sumDepthSource_leftUnit sd se a' c'
local notation "hd" => sumDepthSource_rightUnit sd se a' c'
local notation "hxu" => sumDepthSource_abscissaUnit sd se a' c'
local notation "i" => sumDepthSourceInverse sd se a' c' D.uniformizer_ne_zero hkl
local notation "L" => sumDepthSourceSlope sd se a' c' D.uniformizer_ne_zero hkl
local notation "hi" => sumDepthSourceInverse_relation sd se a' c' D.uniformizer_ne_zero hkl
local notation "hL" => sumDepthSourceSlope_relation sd se a' c' D.uniformizer_ne_zero hkl
local notation "dd" => commonBranchData (k := k) N sd (by omega : k + 2 * k ≤ m)
local notation "ee" => commonBranchData N se hm
local notation "out" => factoredSumDepthOutput D.uniformizer_ne_zero sd se hkl dd ee sz b2 h2
  aa cc hc hd hxu i L hi hL
local notation "X" => factoredSumDepthX sd se dd ee sz b2 aa cc hc hd hxu i
local notation "Y" => factoredSumDepthY sd se dd ee sz b2 aa cc hc hd hxu i L

/-- The actual sum-depth output in the original, unsheared divided coordinates. -/
def nodalFactoredSumSourceOutput : Coordinate W (π ^ (k + l)) z.b3 z.b4 z.b6 →ₐ[R] B :=
  (out).comp (shearForward W (π ^ (k + l)) z.b3 z.b4 z.b6 σ)

/-- Returning through the shear preserves the full sum-depth abscissa. -/
@[simp] theorem nodalFactoredSumSourceOutput_x :
    nodalFactoredSumSourceOutput D d e hkl hm z a c
      (x W (π ^ (k + l)) z.b3 z.b4 z.b6) = X := by
  dsimp only [nodalFactoredSumSourceOutput, AlgHom.comp_apply]
  rw [WeierstrassDilatation.shearForward_x, factoredSumDepthOutput_x]

/-- The ordinate retains the exact integral shear correction. -/
@[simp] theorem nodalFactoredSumSourceOutput_y :
    nodalFactoredSumSourceOutput D d e hkl hm z a c
      (y W (π ^ (k + l)) z.b3 z.b4 z.b6) =
        Y + algebraMap R B σ * X := by
  dsimp only [nodalFactoredSumSourceOutput, AlgHom.comp_apply]
  rw [WeierstrassDilatation.shearForward_y, map_add, map_mul, AlgHom.commutes,
    factoredSumDepthOutput_x, factoredSumDepthOutput_y]

/-- The constructed source has a genuine morphism to the original sum-depth chart. -/
def nodalFactoredSumSourceLift : Spec (.of B) ⟶ chart z :=
  Spec.map (CommRingCat.ofHom (nodalFactoredSumSourceOutput D d e hkl hm z a c).toRingHom)

/-- The original coefficient point is unchanged by normalization and its return. -/
@[reassoc] theorem nodalFactoredSumSourceLift_structure :
    nodalFactoredSumSourceLift D d e hkl hm z a c ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (Coordinate W (π ^ (k + l)) z.b3 z.b4 z.b6))) =
        Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
  WeierstrassIntegralChart.specAlgHom_structure _

local notation "s" => algebraMap R B (π ^ k)
local notation "t" => algebraMap R B (π ^ (l - k))
local notation "w" => algebraMap R B (π ^ (k + l))
local notation "r" => algebraMap R B σ
local notation "ox" => ((j).comp a) (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "oy" => ((j).comp a) (y W (π ^ k) d.b3 d.b4 d.b6)
local notation "ux" => ((j).comp c) (x W (π ^ l) e.b3 e.b4 e.b6)
local notation "uy" => ((j).comp c) (y W (π ^ l) e.b3 e.b4 e.b6)
local notation "W'" => W.map (algebraMap R B)
local notation "sum" => nodalFactoredSumSourceOutput D d e hkl hm z a c

omit [Module.Flat R S] in
/-- The returned slope is the secant of both original, uncontracted inputs. -/
theorem nodalFactoredSumSourceSlope_relation :
    (L + r) * (ox - t * ux) = oy - t * uy := by
  have h := hL
  simp only [AlgHom.comp_apply, branchShearInput_x, branchShearInput_y,
    map_sub, map_mul, AlgHom.commutes] at h ⊢
  linear_combination h

/-- The returned abscissa contracts to the original unsheared secant abscissa. -/
theorem nodalFactoredSumSourceOutput_x_scale :
    w * sum (x W (π ^ (k + l)) z.b3 z.b4 z.b6) =
      (W').toAffine.addX (s * ox) (s * (t * ux)) (L + r) := by
  rw [nodalFactoredSumSourceOutput_x,
    factoredSumDepthX_scale D.uniformizer_ne_zero sd se hkl dd ee sz b2 h2
      aa cc hc hd hxu i L hi hL]
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, (rootShearCurve_coefficients σ).1,
    (rootShearCurve_coefficients σ).2.1, AlgHom.comp_apply, branchShearInput_x,
    map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

/-- The returned ordinate contracts to the same original unsheared secant. -/
theorem nodalFactoredSumSourceOutput_y_scale :
    w * sum (y W (π ^ (k + l)) z.b3 z.b4 z.b6) =
      (W').toAffine.addY (s * ox) (s * (t * ux)) (s * oy) (L + r) := by
  rw [nodalFactoredSumSourceOutput_y]
  calc
    w * (Y + r * X) = w * Y + r * (w * X) := by ring
    _ = _ := by
      rw [factoredSumDepthY_scale D.uniformizer_ne_zero sd se hkl dd ee sz b2 h2
        aa cc hc hd hxu i L hi hL,
        factoredSumDepthX_scale D.uniformizer_ne_zero sd se hkl dd ee sz b2 h2
          aa cc hc hd hxu i L hi hL]
      simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
        WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX,
        WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
        (rootShearCurve_coefficients σ).1, (rootShearCurve_coefficients σ).2.1,
        (rootShearCurve_coefficients σ).2.2.1, AlgHom.comp_apply,
        branchShearInput_x, branchShearInput_y, map_add, map_sub, map_mul, map_pow,
        map_ofNat, AlgHom.commutes]
      ring

end FLT.Mazur.WeierstrassDividedDepth
