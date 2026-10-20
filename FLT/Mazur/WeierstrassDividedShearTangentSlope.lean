/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedShearBranchSource
public import FLT.Mazur.WeierstrassDividedTangentRelations

/-!
# Sheared tangent slopes on their actual common domain

The two tangent denominators need not define the same open. On any common
refinement, their slopes differ by the integral shear parameter, even when
the abscissae coincide. No scale cancellation or reducedness is required.
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

/-- The numerator correction retains both original input ordinates. -/
theorem branchShearInput_numerator :
    dividedTangentNumerator V s b3 (b4 - r * b3) b6 a' c' =
      dividedTangentNumerator W s b3 b4 b6 a c -
        algebraMap R S r * dividedTangentDenominator V s b3 (b4 - r * b3) b6 a' c' +
        algebraMap R S r * (c (y W s b3 b4 b6) - a (y W s b3 b4 b6)) := by
  simp only [dividedTangentNumerator,
    dividedTangentDenominator, branchShearInput_x, branchShearInput_y,
    (rootShearCurve_coefficients r).1, (rootShearCurve_coefficients r).2.1,
    map_sub, map_add, map_mul, map_pow, map_ofNat]
  ring

variable (e : DividedTangentRing (rootShearCurve W r) s b3 (b4 - r * b3) b6
    (branchShearInput W s b3 b4 b6 r a) (branchShearInput W s b3 b4 b6 r c) →ₐ[R] B)
  (f : DividedTangentRing W s b3 b4 b6 a c →ₐ[R] B)
  (h : e.comp (IsScalarTower.toAlgHom R S
      (DividedTangentRing (rootShearCurve W r) s b3 (b4 - r * b3) b6
        (branchShearInput W s b3 b4 b6 r a) (branchShearInput W s b3 b4 b6 r c))) =
    f.comp (IsScalarTower.toAlgHom R S (DividedTangentRing W s b3 b4 b6 a c)))

include h in
/-- The actual localized tangent slopes commute with the original integral shear. -/
theorem dividedShearTangent_slope :
    e (dividedTangentSlope V s b3 (b4 - r * b3) b6 a' c') =
      f (dividedTangentSlope W s b3 b4 b6 a c) - algebraMap R B r := by
  have hj (z : S) : e (algebraMap S T' z) = f (algebraMap S T z) :=
    DFunLike.congr_fun h z
  have he := congrArg e
    (dividedTangentSlope_relation V s b3 (b4 - r * b3) b6 a' c')
  have hf := congrArg f (dividedTangentSlope_relation W s b3 b4 b6 a c)
  have hl := dividedTangentRefinement_line W s b3 b4 b6 a c f
  have hu := (IsLocalization.Away.algebraMap_isUnit
    (S := T') (dividedTangentDenominator V s b3 (b4 - r * b3) b6 a' c')).map e
  apply hu.mul_left_inj.mp
  simp only [map_mul, hj, branchShearInput_numerator, branchShearInput_denominator,
    map_add, map_sub, map_mul, ← IsScalarTower.algebraMap_apply R S T,
    AlgHom.commutes] at he hf ⊢
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at hl
  linear_combination he - hf + algebraMap R B r * hl

end FLT.Mazur.WeierstrassDilatation
