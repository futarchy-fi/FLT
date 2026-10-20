/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecantSource
public import FLT.Mazur.WeierstrassOrdinaryChartSpecialization

/-!
# Divided secants retain the original addition formula

On any ordinary presentation with the same two original inputs, regularity
of the scale identifies the slopes. The actual coordinate maps then agree.
This comparison assumes input compatibility only, never equality of outputs.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
local notation "T" => DividedSecantRing W s b3 b4 b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "orig" => fromOriginal W s b3 b4 b6 h3 h4 h6
local notation "l" => dividedSecantSlope W s b3 b4 b6 a c
variable (b : Bool)
  (f : WeierstrassIntegralChart.additionChartRing W
    (WeierstrassIntegralChart.ordinaryIndex b) →ₐ[R] DividedSecantRing W s b3 b4 b6 a c)
  (ha : f.comp (WeierstrassIntegralChart.ordinaryInputLeft W b) = ((IsScalarTower.toAlgHom R S
    (DividedSecantRing W s b3 b4 b6 a c)).comp a).comp
      (fromOriginal W s b3 b4 b6 h3 h4 h6))
  (hc : f.comp (WeierstrassIntegralChart.ordinaryInputRight W b) = ((IsScalarTower.toAlgHom R S
    (DividedSecantRing W s b3 b4 b6 a c)).comp c).comp
      (fromOriginal W s b3 b4 b6 h3 h4 h6))
  (hs : IsRegular (algebraMap R (DividedSecantRing W s b3 b4 b6 a c) s))

include ha hc hs in
/-- Regularity cancels the common scale in the original ordinary line relation. -/
theorem dividedSecantSlope_eq_ordinary :
    f (WeierstrassIntegralChart.ordinaryChartSlope W b) = l := by
  have hleft (t) : f (WeierstrassIntegralChart.ordinaryInputLeft W b t) =
      ((j).comp a) (orig t) := DFunLike.congr_fun ha t
  have hright (t) : f (WeierstrassIntegralChart.ordinaryInputRight W b t) =
      ((j).comp c) (orig t) := DFunLike.congr_fun hc t
  have he := WeierstrassIntegralChart.ordinarySpecialization_line W b f
  simp only [hleft, hright, fromOriginal_x, fromOriginal_y, map_mul,
    AlgHom.commutes] at he
  have hd : f (WeierstrassIntegralChart.ordinaryChartSlope W b) *
      (((j).comp a) (x W s b3 b4 b6) - ((j).comp c) (x W s b3 b4 b6)) =
        ((j).comp a) (y W s b3 b4 b6) - ((j).comp c) (y W s b3 b4 b6) := by
    apply hs.left
    linear_combination he
  have hu : IsUnit (algebraMap S T (a (x W s b3 b4 b6) - c (x W s b3 b4 b6))) :=
    IsLocalization.Away.algebraMap_isUnit _
  apply hu.mul_left_inj.mp
  rw [map_sub]
  exact hd.trans (dividedSecantSlope_relation W s b3 b4 b6 a c).symm

include ha hc hs in
/-- The new two-divided-input morphism is the original ordinary addition on every such overlap. -/
theorem dividedSecantOutput_eq_ordinary :
    dividedSecantOutput W s b3 b4 b6 a c h3 h4 h6 =
      f.comp (WeierstrassIntegralChart.ordinaryChartAddition W b) := by
  have hleft (t) : f (WeierstrassIntegralChart.ordinaryInputLeft W b t) =
      ((j).comp a) (orig t) := DFunLike.congr_fun ha t
  have hright (t) : f (WeierstrassIntegralChart.ordinaryInputRight W b t) =
      ((j).comp c) (orig t) := DFunLike.congr_fun hc t
  apply WeierstrassIntegralChart.hom_ext
  intro i
  rw [AlgHom.comp_apply, WeierstrassIntegralChart.ordinarySpecialization_coord]
  simp only [hleft, hright, fromOriginal_x, fromOriginal_y, map_mul, AlgHom.commutes,
    dividedSecantSlope_eq_ordinary W s b3 b4 b6 a c h3 h4 h6 b f ha hc hs]
  exact WeierstrassIntegralChart.evaluation_coord W 2 _ _ _ i

end FLT.Mazur.WeierstrassDilatation
