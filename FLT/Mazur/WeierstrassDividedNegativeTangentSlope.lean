/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNegativeBranchSource
public import FLT.Mazur.WeierstrassDividedTangentRelations

/-!
# Actual tangent slopes commute with negating both divided inputs

On a common domain of the original and reversed tangent opens, negating
both inputs changes the constructed slope to minus the old slope minus a₁.
This includes equal abscissae and does not cancel the original scale.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "a'" => branchNegativeInput W s b3 b4 b6 a
local notation "c'" => branchNegativeInput W s b3 b4 b6 c
local notation "T" => DividedTangentRing W s b3 b4 b6 a c
local notation "T'" => DividedTangentRing W s b3 b4 b6 a' c'
variable (e : DividedTangentRing W s b3 b4 b6
    (branchNegativeInput W s b3 b4 b6 a) (branchNegativeInput W s b3 b4 b6 c) →ₐ[R] B)
  (f : DividedTangentRing W s b3 b4 b6 a c →ₐ[R] B)
  (h : e.comp (IsScalarTower.toAlgHom R S
      (DividedTangentRing W s b3 b4 b6
        (branchNegativeInput W s b3 b4 b6 a) (branchNegativeInput W s b3 b4 b6 c))) =
    f.comp (IsScalarTower.toAlgHom R S (DividedTangentRing W s b3 b4 b6 a c)))

include h in
/-- Negating both actual inputs changes the tangent slope by the original negation formula. -/
theorem dividedNegativeTangent_slope :
    e (dividedTangentSlope W s b3 b4 b6 a' c') =
      -f (dividedTangentSlope W s b3 b4 b6 a c) - algebraMap R B W.a₁ := by
  have hj (z : S) : e (algebraMap S T' z) = f (algebraMap S T z) :=
    DFunLike.congr_fun h z
  have he := congrArg e (dividedTangentSlope_relation W s b3 b4 b6 a' c')
  have hf := congrArg f (dividedTangentSlope_relation W s b3 b4 b6 a c)
  have hl := dividedTangentRefinement_line W s b3 b4 b6 a c f
  have hu := (IsLocalization.Away.algebraMap_isUnit
    (S := T') (dividedTangentDenominator W s b3 b4 b6 a' c')).map e
  apply hu.mul_left_inj.mp
  simp only [map_mul, hj, dividedTangentNumerator, dividedTangentDenominator,
    branchNegativeInput_x, branchNegativeInput_y, map_add, map_sub, map_mul, map_pow,
    map_neg, ← IsScalarTower.algebraMap_apply R S T, AlgHom.commutes] at he hf ⊢
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at hl
  linear_combination he - hf - algebraMap R B W.a₁ * hl

end FLT.Mazur.WeierstrassDilatation
