/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReciprocalSecantFormula
public import FLT.Mazur.WeierstrassDividedTangentRelations
public import FLT.Mazur.WeierstrassReciprocalAdditionCompatibility

/-!
# The actual divided reciprocal and tangent formulas on their overlap

Matching full divided input maps identify the two slopes as inverses. Their
homogeneous original outputs differ by the cube of the reciprocal slope,
without cancellation or inversion of the original scale.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassIntegralAddition
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
  (e : DividedReciprocalRing W s b3 b4 b6 a c →ₐ[R] B)
  (f : DividedTangentRing W s b3 b4 b6 a c →ₐ[R] B)
local notation "T" => DividedReciprocalRing W s b3 b4 b6 a c
local notation "V" => DividedTangentRing W s b3 b4 b6 a c
local notation "jt" => IsScalarTower.toAlgHom R S T
local notation "js" => IsScalarTower.toAlgHom R S V
local notation "m" => e (dividedReciprocalSlope W s b3 b4 b6 a c)
local notation "l" => f (dividedTangentSlope W s b3 b4 b6 a c)
variable
  (ha : (e.comp (IsScalarTower.toAlgHom R S
      (DividedReciprocalRing W s b3 b4 b6 a c))).comp a =
    (f.comp (IsScalarTower.toAlgHom R S (DividedTangentRing W s b3 b4 b6 a c))).comp a)
  (hc : (e.comp (IsScalarTower.toAlgHom R S
      (DividedReciprocalRing W s b3 b4 b6 a c))).comp c =
    (f.comp (IsScalarTower.toAlgHom R S (DividedTangentRing W s b3 b4 b6 a c))).comp c)

include ha hc in
/-- The actual reciprocal and tangent slopes are inverse on their entire common source. -/
theorem dividedReciprocalTangent_inverse : m * l = 1 := by
  have ht := congrArg e (dividedReciprocalSlope_line W s b3 b4 b6 a c)
  have hs := dividedTangentRefinement_line W s b3 b4 b6 a c f
  have hl (z) : e (jt (a z)) = f (js (a z)) := DFunLike.congr_fun ha z
  have hr (z) : e (jt (c z)) = f (js (c z)) := DFunLike.congr_fun hc z
  simp only [map_mul, map_sub, AlgHom.comp_apply, hl, hr] at ht
  simp only [AlgHom.comp_apply] at hs
  have hu := (dividedReciprocal_difference_isUnit W s b3 b4 b6 a c).map e
  simp only [map_sub, AlgHom.comp_apply, hl, hr] at hu
  have hm := inverse_slopes_of_relations hu ht hs
  simpa only [mul_comm] using hm

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

include ha hc in
/-- The two actual original outputs have the precise homogeneous scale on the overlap. -/
theorem dividedReciprocalTangent_scaled (i : Fin 3) :
    e (dividedReciprocalCoordinates W s b3 b4 b6 a c i) =
      m ^ 3 * f (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6
        (WeierstrassIntegralChart.coord W 2 i)) := by
  have hl (z) : e (jt (a z)) = f (js (a z)) := DFunLike.congr_fun ha z
  have hr (z) : e (jt (c z)) = f (js (c z)) := DFunLike.congr_fun hc z
  rw [dividedReciprocalRefinement_coordinates, hl, hl, hr]
  have h := congrFun (reciprocalXYZ_eq_scaled_add (W.map (algebraMap R B))
    (algebraMap R B s * f (js (a (x W s b3 b4 b6))))
    (algebraMap R B s * f (js (c (x W s b3 b4 b6))))
    (algebraMap R B s * f (js (a (y W s b3 b4 b6)))) l m
    (dividedReciprocalTangent_inverse W s b3 b4 b6 a c e f ha hc)) i
  rw [h]
  fin_cases i <;>
    simp [dividedTangentOutput, WeierstrassIntegralChart.evaluation_coord,
      dividedTangentX, dividedTangentY, Affine.addX, Affine.addY, Affine.negY,
      Affine.negAddY, AlgHom.comp_apply]

end FLT.Mazur.WeierstrassDilatation
