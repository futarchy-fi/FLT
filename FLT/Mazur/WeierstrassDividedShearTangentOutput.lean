/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedShearTangentSlope
public import FLT.Mazur.WeierstrassAffineVariableChangeMap

/-!
# Original cubic outputs commute with integral tangent shear

On every affine common refinement, the two actual coordinate-algebra maps
agree after the original cubic variable change. The equality retains
nilpotents and includes coincident abscissae.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve
universe u
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] (W : WeierstrassCurve R) (s b3 b4 b6 r : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "V" => rootShearCurve W r
local notation "a'" => branchShearInput W s b3 b4 b6 r a
local notation "c'" => branchShearInput W s b3 b4 b6 r c
local notation "T" => DividedTangentRing W s b3 b4 b6 a c
local notation "T'" => DividedTangentRing V s b3 (b4 - r * b3) b6 a' c'

variable (e : DividedTangentRing (rootShearCurve W r) s b3 (b4 - r * b3) b6
    (branchShearInput W s b3 b4 b6 r a) (branchShearInput W s b3 b4 b6 r c) →ₐ[R] B)
  (f : DividedTangentRing W s b3 b4 b6 a c →ₐ[R] B)
  (h : e.comp (IsScalarTower.toAlgHom R S
      (DividedTangentRing (rootShearCurve W r) s b3 (b4 - r * b3) b6
        (branchShearInput W s b3 b4 b6 r a) (branchShearInput W s b3 b4 b6 r c))) =
    f.comp (IsScalarTower.toAlgHom R S (DividedTangentRing W s b3 b4 b6 a c)))


variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (h3' : (rootShearCurve W r).a₃ = s * b3)
  (h4' : (rootShearCurve W r).a₄ = s * (b4 - r * b3))
  (h6' : (rootShearCurve W r).a₆ = s ^ 2 * b6)
local notation "C" => (WeierstrassCurve.VariableChange.mk 1 0 r 0)
local notation "hv" => (show C • W = V by unfold rootShearCurve; rfl)

include h in
/-- Both actual affine cubic outputs agree in the original unsheared coordinates. -/
theorem dividedShearTangent_output :
    (e.comp (dividedTangentOutput V s b3 (b4 - r * b3) b6 a' c' h3' h4' h6')).comp
        (WeierstrassIntegralChart.affineVariableChangeMap W V C hv) =
      f.comp (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6) := by
  have hj (z : S) : e (algebraMap S T' z) = f (algebraMap S T z) :=
    DFunLike.congr_fun h z
  have hl := dividedShearTangent_slope W s b3 b4 b6 r a c e f h
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i
  · change e ((dividedTangentOutput V s b3 (b4 - r * b3) b6 a' c' h3' h4' h6')
        (WeierstrassIntegralChart.affineVariableChangeMap W V C hv
          (WeierstrassIntegralChart.coord W 2 0))) =
      f (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6
        (WeierstrassIntegralChart.coord W 2 0))
    simp only [WeierstrassIntegralChart.affineVariableChangeMap_x, Units.val_one, map_one, map_zero,
      one_pow, one_mul, add_zero, dividedTangentOutput,
      WeierstrassIntegralChart.evaluation_coord, Matrix.cons_val_zero]
    simp only [WeierstrassCurve.toAffine, dividedTangentX, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
      map_add, map_sub, map_mul, map_pow, AlgHom.commutes, hl,
      branchShearInput_x, hj, (rootShearCurve_coefficients r).1,
      (rootShearCurve_coefficients r).2.1, map_ofNat]
    ring
  · change e ((dividedTangentOutput V s b3 (b4 - r * b3) b6 a' c' h3' h4' h6')
        (WeierstrassIntegralChart.affineVariableChangeMap W V C hv
          (WeierstrassIntegralChart.coord W 2 1))) =
      f (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6
        (WeierstrassIntegralChart.coord W 2 1))
    simp only [WeierstrassIntegralChart.affineVariableChangeMap_y,
      map_add, map_mul, AlgHom.commutes, Units.val_one, map_one, map_zero,
      one_pow, one_mul, add_zero, dividedTangentOutput,
      WeierstrassIntegralChart.evaluation_coord, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [WeierstrassCurve.toAffine, dividedTangentX, dividedTangentY,
      WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom', map_add, map_sub, map_mul, map_pow, map_neg,
      AlgHom.commutes, hl, branchShearInput_x, branchShearInput_y, hj,
      (rootShearCurve_coefficients r).1, (rootShearCurve_coefficients r).2.1,
      (rootShearCurve_coefficients r).2.2.1, map_ofNat]
    ring
  · change e ((dividedTangentOutput V s b3 (b4 - r * b3) b6 a' c' h3' h4' h6')
        (WeierstrassIntegralChart.affineVariableChangeMap W V C hv
          (WeierstrassIntegralChart.coord W 2 2))) =
      f (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6
        (WeierstrassIntegralChart.coord W 2 2))
    simp only [WeierstrassIntegralChart.coord_self, map_one]

end FLT.Mazur.WeierstrassDilatation
