/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentRelations
public import FLT.Mazur.WeierstrassDividedSecantSource

/-!
# Tangent and secant outputs agree on their affine overlaps

Two maps from the actual slope localizations with the same divided inputs
have the same slope and original output. The scale need not be regular or a unit.
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
  (f : DividedSecantRing W s b3 b4 b6 a c →ₐ[R] B)
local notation "T" => DividedTangentRing W s b3 b4 b6 a c
local notation "V" => DividedSecantRing W s b3 b4 b6 a c
local notation "jt" => IsScalarTower.toAlgHom R S T
local notation "js" => IsScalarTower.toAlgHom R S V
variable
  (ha : (e.comp (IsScalarTower.toAlgHom R S
      (DividedTangentRing W s b3 b4 b6 a c))).comp a =
    (f.comp (IsScalarTower.toAlgHom R S (DividedSecantRing W s b3 b4 b6 a c))).comp a)
  (hc : (e.comp (IsScalarTower.toAlgHom R S
      (DividedTangentRing W s b3 b4 b6 a c))).comp c =
    (f.comp (IsScalarTower.toAlgHom R S (DividedSecantRing W s b3 b4 b6 a c))).comp c)

include ha hc in
/-- Matching divided inputs identify the actual slopes on the tangent/secant overlap. -/
theorem dividedTangentSecant_slope :
    e (dividedTangentSlope W s b3 b4 b6 a c) =
      f (dividedSecantSlope W s b3 b4 b6 a c) := by
  have ht := dividedTangentRefinement_line W s b3 b4 b6 a c e
  rw [ha, hc] at ht
  have hs := congrArg f (dividedSecantSlope_relation W s b3 b4 b6 a c)
  simp only [map_mul, map_sub] at hs
  have hu := (IsLocalization.Away.algebraMap_isUnit (S := V)
    (a (x W s b3 b4 b6) - c (x W s b3 b4 b6))).map f
  apply hu.mul_left_inj.mp
  simpa only [map_sub, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] using
    ht.trans hs.symm

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

include ha hc in
/-- The actual algebra maps to the unchanged original cubic agree on every affine overlap. -/
theorem dividedTangentSecant_output :
    e.comp (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6) =
      f.comp (dividedSecantOutput W s b3 b4 b6 a c h3 h4 h6) := by
  have hl (z) : e (algebraMap S T (a z)) = f (algebraMap S V (a z)) := DFunLike.congr_fun ha z
  have hr (z) : e (algebraMap S T (c z)) = f (algebraMap S V (c z)) := DFunLike.congr_fun hc z
  apply WeierstrassIntegralChart.hom_ext
  intro i
  simp only [AlgHom.comp_apply, dividedTangentOutput, dividedSecantOutput,
    WeierstrassIntegralChart.evaluation_coord]
  fin_cases i <;>
    simp [dividedTangentX, dividedTangentY, dividedSecantX, dividedSecantY,
      Affine.addX, Affine.addY, Affine.negY, Affine.negAddY, AlgHom.commutes,
      hl, hr, dividedTangentSecant_slope W s b3 b4 b6 a c e f ha hc]

end FLT.Mazur.WeierstrassDilatation
