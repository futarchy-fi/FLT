/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentRelations

/-!
# Reversed tangent outputs on their actual common domain

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
  (f : DividedTangentRing W s b3 b4 b6 c a →ₐ[R] B)
local notation "T" => DividedTangentRing W s b3 b4 b6 a c
local notation "V" => DividedTangentRing W s b3 b4 b6 c a
local notation "jt" => IsScalarTower.toAlgHom R S T
local notation "jr" => IsScalarTower.toAlgHom R S V
variable (h : e.comp (IsScalarTower.toAlgHom R S
    (DividedTangentRing W s b3 b4 b6 a c)) =
  f.comp (IsScalarTower.toAlgHom R S (DividedTangentRing W s b3 b4 b6 c a)))

include h in
/-- Reversing the inputs preserves the slope wherever both tangent denominators are units. -/
theorem dividedTangentReverse_slope :
    e (dividedTangentSlope W s b3 b4 b6 a c) =
      f (dividedTangentSlope W s b3 b4 b6 c a) := by
  have ht := dividedTangentRefinement_chord W s b3 b4 b6 a c e
  have hr := dividedTangentRefinement_chord W s b3 b4 b6 c a f
  have hl := dividedTangentRefinement_line W s b3 b4 b6 c a f
  rw [h] at ht
  have hu := dividedTangentRefinement_denominator_isUnit W s b3 b4 b6 a c e
  rw [h] at hu
  apply hu.mul_left_inj.mp
  linear_combination ht - hr - algebraMap R B W.a₁ * hl

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

include h in
/-- The actual original cubic outputs agree after reversing the two full divided inputs. -/
theorem dividedTangentReverse_output :
    e.comp (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6) =
      f.comp (dividedTangentOutput W s b3 b4 b6 c a h3 h4 h6) := by
  have he (z) : e (algebraMap S T z) = f (algebraMap S V z) := DFunLike.congr_fun h z
  have hl := dividedTangentRefinement_line W s b3 b4 b6 c a f
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at hl
  apply WeierstrassIntegralChart.hom_ext
  intro i
  simp only [AlgHom.comp_apply, dividedTangentOutput, WeierstrassIntegralChart.evaluation_coord]
  fin_cases i
  · change e (dividedTangentX W s b3 b4 b6 a c) =
      f (dividedTangentX W s b3 b4 b6 c a)
    simp only [dividedTangentX, Affine.addX, map_sub, map_add, map_mul, map_pow,
      AlgHom.commutes, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', he,
      dividedTangentReverse_slope W s b3 b4 b6 a c e f h, toAffine, map_a₁, map_a₂]
    ring
  · change e (dividedTangentY W s b3 b4 b6 a c) =
      f (dividedTangentY W s b3 b4 b6 c a)
    simp only [dividedTangentY, Affine.addY, Affine.negY, Affine.negAddY, Affine.addX,
      map_sub, map_neg, map_add, map_mul, map_pow, AlgHom.commutes, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom', he,
      dividedTangentReverse_slope W s b3 b4 b6 a c e f h, toAffine, map_a₁, map_a₂, map_a₃]
    linear_combination -algebraMap R B s * hl
  · simp

end FLT.Mazur.WeierstrassDilatation
