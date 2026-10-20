/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentOriginalRelations
public import FLT.Mazur.WeierstrassDividedReciprocalOriginalRelations

/-!
# Reciprocal and tangent formulas across distinct divided scales

Matching original cubic inputs identify the slopes as inverses. Their actual
homogeneous outputs agree up to the cube of the reciprocal slope.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S S' B : Type u} [CommRing R] [CommRing S] [CommRing S'] [CommRing B]
  [Algebra R S] [Algebra R S'] [Algebra R B]
  (W : WeierstrassCurve R) (s b3 b4 b6 t c3 c4 c6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
  (a₂ c₂ : Coordinate W t c3 c4 c6 →ₐ[R] S')
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (k3 : W.a₃ = t * c3) (k4 : W.a₄ = t * c4) (k6 : W.a₆ = t ^ 2 * c6)
  (e : DividedReciprocalRing W s b3 b4 b6 a c →ₐ[R] B)
  (f : DividedTangentRing W t c3 c4 c6 a₂ c₂ →ₐ[R] B)
local notation "T" => DividedReciprocalRing W s b3 b4 b6 a c
local notation "V" => DividedTangentRing W t c3 c4 c6 a₂ c₂
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "j₂" => IsScalarTower.toAlgHom R S' V
local notation "orig" => fromOriginal W s b3 b4 b6 h3 h4 h6
local notation "orig₂" => fromOriginal W t c3 c4 c6 k3 k4 k6
variable
  (ha : (((e.comp (IsScalarTower.toAlgHom R S
      (DividedReciprocalRing W s b3 b4 b6 a c))).comp a).comp
        (fromOriginal W s b3 b4 b6 h3 h4 h6)) =
    (((f.comp (IsScalarTower.toAlgHom R S'
      (DividedTangentRing W t c3 c4 c6 a₂ c₂))).comp a₂).comp
        (fromOriginal W t c3 c4 c6 k3 k4 k6)))
  (hc : (((e.comp (IsScalarTower.toAlgHom R S
      (DividedReciprocalRing W s b3 b4 b6 a c))).comp c).comp
        (fromOriginal W s b3 b4 b6 h3 h4 h6)) =
    (((f.comp (IsScalarTower.toAlgHom R S'
      (DividedTangentRing W t c3 c4 c6 a₂ c₂))).comp c₂).comp
        (fromOriginal W t c3 c4 c6 k3 k4 k6)))
  (hs : IsRegular (algebraMap R B s))

local notation "m" => e (dividedReciprocalSlope W s b3 b4 b6 a c)
local notation "l" => f (dividedTangentSlope W t c3 c4 c6 a₂ c₂)

include ha hc hs in
/-- Reciprocal and tangent slopes at different depths are inverse on their common source. -/
theorem dividedCrossDepthReciprocalTangent_inverse : m * l = 1 := by
  apply dividedReciprocalRefinement_inverse_of_original_line
    W s b3 b4 b6 a c h3 h4 h6 e hs
  rw [ha, hc]
  exact dividedTangentRefinement_original_line W t c3 c4 c6 a₂ c₂ k3 k4 k6 f

include ha hc hs in
/-- The homogeneous reciprocal output has the precise scale of the other-depth tangent output. -/
theorem dividedCrossDepthReciprocalTangent_scaled (i : Fin 3) :
    e (dividedReciprocalCoordinates W s b3 b4 b6 a c i) =
      m ^ 3 * f (dividedTangentOutput W t c3 c4 c6 a₂ c₂ k3 k4 k6
        (WeierstrassIntegralChart.coord W 2 i)) := by
  rw [dividedReciprocalRefinement_original_coord W s b3 b4 b6 a c h3 h4 h6, ha, hc]
  have ho := dividedTangentRefinement_original_coord W t c3 c4 c6 a₂ c₂ k3 k4 k6 f i
  dsimp only [AlgHom.comp_apply] at ho
  rw [ho]
  exact congrFun (WeierstrassIntegralAddition.reciprocalXYZ_eq_scaled_add
    (W.map (algebraMap R B)) _ _ _ l m
    (dividedCrossDepthReciprocalTangent_inverse W s b3 b4 b6 t c3 c4 c6 a c a₂ c₂
      h3 h4 h6 k3 k4 k6 e f ha hc hs)) i

end FLT.Mazur.WeierstrassDilatation
