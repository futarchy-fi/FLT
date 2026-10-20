/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentRelations
public import FLT.Mazur.WeierstrassDividedSecantOriginalAction

/-!
# Tangent and reversed secant outputs on their common domain

The reversed denominator need only be invertible on the overlap. The line
relation identifies the slopes and outputs without cancelling the scale.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
  (e : DividedTangentRing W s b3 b4 b6 a c →ₐ[R] B)
  (f : DividedSecantRing W s b3 b4 b6 c a →ₐ[R] B)
local notation "T" => DividedTangentRing W s b3 b4 b6 a c
local notation "V" => DividedSecantRing W s b3 b4 b6 c a
local notation "jt" => IsScalarTower.toAlgHom R S T
local notation "jr" => IsScalarTower.toAlgHom R S V
variable (h : e.comp (IsScalarTower.toAlgHom R S
    (DividedTangentRing W s b3 b4 b6 a c)) =
  f.comp (IsScalarTower.toAlgHom R S (DividedSecantRing W s b3 b4 b6 c a)))

include h in
/-- Reversing the inputs preserves the slope wherever the secant denominator is a unit. -/
theorem dividedTangentReverseSecant_slope :
    e (dividedTangentSlope W s b3 b4 b6 a c) =
      f (dividedSecantSlope W s b3 b4 b6 c a) := by
  have ht := dividedTangentRefinement_line W s b3 b4 b6 a c e
  rw [h] at ht
  have hr := congrArg f (dividedSecantSlope_relation W s b3 b4 b6 c a)
  simp only [map_mul, map_sub, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at hr ht
  have hu := dividedSecantRefinement_difference_isUnit W s b3 b4 b6 c a f
  apply hu.mul_left_inj.mp
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
  linear_combination -ht - hr

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

include h in
/-- The actual original cubic outputs agree after reversing the two full divided inputs. -/
theorem dividedTangentReverseSecant_output :
    e.comp (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6) =
      f.comp (dividedSecantOutput W s b3 b4 b6 c a h3 h4 h6) := by
  have he (z) : e (algebraMap S T z) = f (algebraMap S V z) := DFunLike.congr_fun h z
  have hl := congrArg f (dividedSecantSlope_relation W s b3 b4 b6 c a)
  simp only [map_mul, map_sub, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at hl
  apply WeierstrassIntegralChart.hom_ext
  intro i
  simp only [AlgHom.comp_apply, dividedTangentOutput, dividedSecantOutput,
    WeierstrassIntegralChart.evaluation_coord]
  fin_cases i
  · change e (dividedTangentX W s b3 b4 b6 a c) =
      f (dividedSecantX W s b3 b4 b6 c a)
    simp only [dividedTangentX, dividedSecantX, Affine.addX, map_sub, map_add, map_mul, map_pow,
      AlgHom.commutes, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', he,
      dividedTangentReverseSecant_slope W s b3 b4 b6 a c e f h, toAffine, map_a₁, map_a₂]
    ring
  · change e (dividedTangentY W s b3 b4 b6 a c) =
      f (dividedSecantY W s b3 b4 b6 c a)
    simp only [dividedTangentY, dividedSecantY, Affine.addY, Affine.negY,
      Affine.negAddY, Affine.addX,
      map_sub, map_neg, map_add, map_mul, map_pow, AlgHom.commutes, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom', he,
      dividedTangentReverseSecant_slope W s b3 b4 b6 a c e f h, toAffine, map_a₁, map_a₂, map_a₃]
    linear_combination -algebraMap R B s * hl
  · simp

end FLT.Mazur.WeierstrassDilatation
