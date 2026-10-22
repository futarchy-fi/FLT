/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalReflectedSecant

/-!
# Original secant contraction of the normalized reflected output

The normalized output, returned to the original curve, contracts to the
original secant as an equality of complete algebra maps and scheme morphisms.
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
  (hkl : k ≤ l) (hl : 2 * l ≤ m) (hm : m ≤ k + 2 * l)
  (z : Data W π (m - k - l))
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "σ" => nodalSecondShear D (m - 2 * l)
local notation "V" => rootShearCurve W σ
local notation "sd" => (⟨d.b3, d.b4 - σ * d.b3, d.b6,
  (shearData d σ).factor3, (shearData d σ).factor4,
  (shearData d σ).factor6⟩ : Data V π k)
local notation "se" => (⟨e.b3, e.b4 - σ * e.b3, e.b6,
  (shearData e σ).factor3, (shearData e σ).factor4,
  (shearData e σ).factor6⟩ : Data V π l)
local notation "sz" => (⟨z.b3, z.b4 - σ * z.b3, z.b6,
  (shearData z σ).factor3, (shearData z σ).factor4,
  (shearData z σ).factor6⟩ : Data V π (m - k - l))
local notation "N" => nodalSecondShear_depth D (m - 2 * l)
local notation "b2" => nodalSecondQuotient D (m - 2 * l)
local notation "h2" => nodalSecondQuotient_factor D (m - 2 * l)
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
local notation "out" => nodalReflectedSourceOutput D d e hkl hl hm z a c
local notation "res" => nodalReflectedSecantRestriction D d e hkl a c
local notation "c₀" => unequalDepthRight D.uniformizer_ne_zero d e hkl c
local notation "old" => dividedSecantOutput W (π ^ k) d.b3 d.b4 d.b6 a c₀
  d.factor3 d.factor4 d.factor6

/-- Both original affine coordinates agree with the restricted original secant. -/
theorem nodalReflectedSourceOutput_original :
    (out).comp (fromOriginal W (π ^ (m - k - l)) z.b3 z.b4 z.b6
      z.factor3 z.factor4 z.factor6) = (res).comp old := by
  apply WeierstrassIntegralChart.hom_ext
  intro v
  fin_cases v
  · change out (fromOriginal W (π ^ (m - k - l)) z.b3 z.b4 z.b6
        z.factor3 z.factor4 z.factor6 (WeierstrassIntegralChart.coord W 2 0)) =
      res (old (WeierstrassIntegralChart.coord W 2 0))
    simp only [fromOriginal_x, map_mul, AlgHom.commutes,
      dividedSecantOutput, WeierstrassIntegralChart.evaluation_coord, Matrix.cons_val_zero]
    rw [nodalReflectedSourceOutput_x_scale D d e hkl hl hm z a c]
    simp only [dividedSecantX, WeierstrassCurve.Affine.addX, map_sub, map_add, map_mul,
      map_pow, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, AlgHom.commutes,
      AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', nodalReflectedSecantRestriction_source,
      unequalDepthRight_x, nodalReflectedSecantRestriction_slope]
  · change out (fromOriginal W (π ^ (m - k - l)) z.b3 z.b4 z.b6
        z.factor3 z.factor4 z.factor6 (WeierstrassIntegralChart.coord W 2 1)) =
      res (old (WeierstrassIntegralChart.coord W 2 1))
    simp only [fromOriginal_y, map_mul, AlgHom.commutes,
      dividedSecantOutput, WeierstrassIntegralChart.evaluation_coord,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [nodalReflectedSourceOutput_y_scale D d e hkl hl hm z a c]
    simp only [dividedSecantY, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX,
      map_sub, map_add, map_mul, map_pow, map_neg, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, AlgHom.commutes,
      AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', nodalReflectedSecantRestriction_source,
      unequalDepthRight_x, nodalReflectedSecantRestriction_slope]
  · change ((out).comp (fromOriginal W (π ^ (m - k - l)) z.b3 z.b4 z.b6
        z.factor3 z.factor4 z.factor6)) (WeierstrassIntegralChart.coord W 2 2) =
      ((res).comp old) (WeierstrassIntegralChart.coord W 2 2)
    rw [WeierstrassIntegralChart.coord_self, map_one, map_one]

/-- Contraction recovers the original scheme-valued secant on the actual source. -/
@[reassoc] theorem nodalReflectedSourceLift_contraction :
    nodalReflectedSourceLift D d e hkl hl hm z a c ≫ toCurve z =
      Spec.map (CommRingCat.ofHom (res).toRingHom) ≫
        dividedSecantToCurve W (π ^ k) d.b3 d.b4 d.b6 a c₀
          d.factor3 d.factor4 d.factor6 := by
  unfold nodalReflectedSourceLift toCurve WeierstrassDilatation.toCurve dividedSecantToCurve
  simp only [← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((out).comp
    (fromOriginal W (π ^ (m - k - l)) z.b3 z.b4 z.b6
      z.factor3 z.factor4 z.factor6)).toRingHom) ≫ _ = _
  rw [nodalReflectedSourceOutput_original]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
