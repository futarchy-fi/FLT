/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentOriginalRelations

/-!
# Tangent formulas agree across distinct divided scales

Equality of the original cubic inputs, rather than equality of divided
coordinates, identifies the actual outputs. Only one scale must remain regular.
The two source algebras and both sets of divided coefficient quotients may differ.
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
  (e : DividedTangentRing W s b3 b4 b6 a c →ₐ[R] B)
  (f : DividedTangentRing W t c3 c4 c6 a₂ c₂ →ₐ[R] B)
local notation "T" => DividedTangentRing W s b3 b4 b6 a c
local notation "V" => DividedTangentRing W t c3 c4 c6 a₂ c₂
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "j₂" => IsScalarTower.toAlgHom R S' V
local notation "orig" => fromOriginal W s b3 b4 b6 h3 h4 h6
local notation "orig₂" => fromOriginal W t c3 c4 c6 k3 k4 k6
variable
  (ha : (((e.comp (IsScalarTower.toAlgHom R S
      (DividedTangentRing W s b3 b4 b6 a c))).comp a).comp
        (fromOriginal W s b3 b4 b6 h3 h4 h6)) =
    (((f.comp (IsScalarTower.toAlgHom R S'
      (DividedTangentRing W t c3 c4 c6 a₂ c₂))).comp a₂).comp
        (fromOriginal W t c3 c4 c6 k3 k4 k6)))
  (hc : (((e.comp (IsScalarTower.toAlgHom R S
      (DividedTangentRing W s b3 b4 b6 a c))).comp c).comp
        (fromOriginal W s b3 b4 b6 h3 h4 h6)) =
    (((f.comp (IsScalarTower.toAlgHom R S'
      (DividedTangentRing W t c3 c4 c6 a₂ c₂))).comp c₂).comp
        (fromOriginal W t c3 c4 c6 k3 k4 k6)))
  (hs : IsRegular (algebraMap R B s))

include ha hc hs in
/-- Matching original inputs determine equal tangent slopes at independent divided scales. -/
theorem dividedCrossDepthTangent_slope :
    e (dividedTangentSlope W s b3 b4 b6 a c) =
      f (dividedTangentSlope W t c3 c4 c6 a₂ c₂) := by
  symm
  apply dividedTangentRefinement_eq_of_original_chord W s b3 b4 b6 a c h3 h4 h6 e hs
  rw [ha, hc]
  exact dividedTangentRefinement_original_chord W t c3 c4 c6 a₂ c₂ k3 k4 k6 f

include ha hc hs in
/-- Actual original outputs agree for divided inputs of different depths. -/
theorem dividedCrossDepthTangent_output :
    e.comp (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6) =
      f.comp (dividedTangentOutput W t c3 c4 c6 a₂ c₂ k3 k4 k6) := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  rw [dividedTangentRefinement_original_coord, dividedTangentRefinement_original_coord,
    ha, hc, dividedCrossDepthTangent_slope W s b3 b4 b6 t c3 c4 c6 a c a₂ c₂
      h3 h4 h6 k3 k4 k6 e f ha hc hs]

end FLT.Mazur.WeierstrassDilatation
