/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReflectedSource

/-!
# Contraction of the constructed reflected-depth output

The entire algebra map recovers the original secant after restricting to
the actual source open. The resulting equality is an equality of scheme
morphisms, including at singular contracted output points.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {W : WeierstrassCurve R} {π : R} {k l m : ℕ} (d : Data W π k) (e : Data W π l)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "B" => SumDepthSourceRing d e a c
local notation "j" => IsScalarTower.toAlgHom R S B
local notation "a'" => (j).comp a
local notation "c'" => (j).comp c

variable [IsDomain R] [IsLocalRing R] [Module.Flat R S]
  (D : SplitNodeDepth W π m) (hkl : k ≤ l) (hl : 2 * l ≤ m) (hm : m ≤ k + 2 * l)
  (z : Data W π (m - k - l))
  (h2 : W.a₂ = 0)
local notation "hc" => sumDepthSource_leftUnit d e a c
local notation "hd" => sumDepthSource_rightUnit d e a c
local notation "hxu" => sumDepthSource_abscissaUnit d e a c
local notation "i" => sumDepthSourceInverse d e a c D.uniformizer_ne_zero hkl
local notation "L" => sumDepthSourceSlope d e a c D.uniformizer_ne_zero hkl
local notation "hi" => sumDepthSourceInverse_relation d e a c D.uniformizer_ne_zero hkl
local notation "hL" => sumDepthSourceSlope_relation d e a c D.uniformizer_ne_zero hkl

local notation "out" => reflectedSourceOutput d e a c D hkl hl hm z h2
local notation "res" => sumDepthSourceRestriction d e a c D.uniformizer_ne_zero hkl
local notation "c₀" => unequalDepthRight D.uniformizer_ne_zero d e hkl c
local notation "old" => dividedSecantOutput W (π ^ k) d.b3 d.b4 d.b6 a c₀
  d.factor3 d.factor4 d.factor6

/-- Both original affine coordinates agree with the restricted original secant. -/
theorem reflectedSourceOutput_original :
    (out).comp (fromOriginal W (π ^ (m - k - l)) z.b3 z.b4 z.b6
      z.factor3 z.factor4 z.factor6) = (res).comp old := by
  apply WeierstrassIntegralChart.hom_ext
  intro v
  fin_cases v
  · change out (fromOriginal W (π ^ (m - k - l)) z.b3 z.b4 z.b6
        z.factor3 z.factor4 z.factor6 (WeierstrassIntegralChart.coord W 2 0)) =
      res (old (WeierstrassIntegralChart.coord W 2 0))
    simp only [fromOriginal_x, map_mul, AlgHom.commutes, reflectedSourceOutput_x,
      dividedSecantOutput, WeierstrassIntegralChart.evaluation_coord, Matrix.cons_val_zero]
    rw [nodeReflectedX_scale D d e hkl hl hm h2 a' c' hc hd hxu i L hi hL]
    simp only [dividedSecantX, WeierstrassCurve.Affine.addX, map_sub, map_add, map_mul,
      map_pow, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, AlgHom.commutes,
      AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', sumDepthSourceRestriction_source,
      unequalDepthRight_x, sumDepthSourceSlope]
  · change out (fromOriginal W (π ^ (m - k - l)) z.b3 z.b4 z.b6
        z.factor3 z.factor4 z.factor6 (WeierstrassIntegralChart.coord W 2 1)) =
      res (old (WeierstrassIntegralChart.coord W 2 1))
    simp only [fromOriginal_y, map_mul, AlgHom.commutes, reflectedSourceOutput_y,
      dividedSecantOutput, WeierstrassIntegralChart.evaluation_coord,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [nodeReflectedY_scale D d e hkl hl hm z h2 a' c' hc hd hxu i L hi hL]
    simp only [dividedSecantY, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX,
      map_sub, map_add, map_mul, map_pow, map_neg, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, AlgHom.commutes,
      AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', sumDepthSourceRestriction_source,
      unequalDepthRight_x, sumDepthSourceSlope]
  · change ((out).comp (fromOriginal W (π ^ (m - k - l)) z.b3 z.b4 z.b6
        z.factor3 z.factor4 z.factor6)) (WeierstrassIntegralChart.coord W 2 2) =
      ((res).comp old) (WeierstrassIntegralChart.coord W 2 2)
    rw [WeierstrassIntegralChart.coord_self, map_one, map_one]

/-- Contraction recovers the original scheme-valued secant on the actual source. -/
@[reassoc] theorem reflectedSourceLift_contraction :
    reflectedSourceLift d e a c D hkl hl hm z h2 ≫ toCurve z =
      Spec.map (CommRingCat.ofHom (res).toRingHom) ≫
        dividedSecantToCurve W (π ^ k) d.b3 d.b4 d.b6 a c₀
          d.factor3 d.factor4 d.factor6 := by
  unfold reflectedSourceLift toCurve WeierstrassDilatation.toCurve dividedSecantToCurve
  simp only [← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((out).comp
    (fromOriginal W (π ^ (m - k - l)) z.b3 z.b4 z.b6
      z.factor3 z.factor4 z.factor6)).toRingHom) ≫ _ = _
  rw [reflectedSourceOutput_original]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
