/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecantSource

/-!
# Original-coordinate relations for divided secant refinements

The slope satisfies the original line and chord equations at every divided
scale. A regular scale makes the original line relation determine this slope,
including on refinements whose original inputs lie above the singular point.
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
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (e : DividedSecantRing W s b3 b4 b6 a c →ₐ[R] B)
local notation "T" => DividedSecantRing W s b3 b4 b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "a'" => (e.comp j).comp a
local notation "c'" => (e.comp j).comp c
local notation "orig" => fromOriginal W s b3 b4 b6 h3 h4 h6
local notation "A" => (a').comp orig
local notation "C" => (c').comp orig
local notation "x₀" => WeierstrassIntegralChart.coord W 2 0
local notation "y₀" => WeierstrassIntegralChart.coord W 2 1
local notation "l" => e (dividedSecantSlope W s b3 b4 b6 a c)
local notation "q" => algebraMap R B s

/-- The divided line equation survives every affine refinement. -/
theorem dividedSecantRefinement_line :
    l * (a' (x W s b3 b4 b6) - c' (x W s b3 b4 b6)) =
      a' (y W s b3 b4 b6) - c' (y W s b3 b4 b6) := by
  have h := congrArg e (dividedSecantSlope_relation W s b3 b4 b6 a c)
  simpa only [map_mul, map_sub, AlgHom.comp_apply] using h

/-- The secant denominator remains a unit after every affine refinement. -/
theorem dividedSecantRefinement_denominator_isUnit :
    IsUnit (a' (x W s b3 b4 b6) - c' (x W s b3 b4 b6)) := by
  have h := (IsLocalization.Away.algebraMap_isUnit (S := T)
    (a (x W s b3 b4 b6) - c (x W s b3 b4 b6))).map e
  simpa only [map_sub, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] using h

/-- The divided slope satisfies the line equation in the unchanged original coordinates. -/
theorem dividedSecantRefinement_original_line :
    l * (A x₀ - C x₀) = A y₀ - C y₀ := by
  simp only [AlgHom.comp_apply, fromOriginal_x, fromOriginal_y, map_mul, AlgHom.commutes]
  have h := dividedSecantRefinement_line W s b3 b4 b6 a c e
  simp only [AlgHom.comp_apply] at h
  linear_combination q * h

/-- The divided chord equation scales to the original cubic chord equation. -/
theorem dividedSecantRefinement_original_chord :
    l * (A y₀ + C y₀ + algebraMap R B W.a₁ * C x₀ + algebraMap R B W.a₃) =
      A x₀ ^ 2 + A x₀ * C x₀ + C x₀ ^ 2 +
        algebraMap R B W.a₂ * (A x₀ + C x₀) + algebraMap R B W.a₄ -
          algebraMap R B W.a₁ * A y₀ := by
  simp only [AlgHom.comp_apply, fromOriginal_x, fromOriginal_y, h3, h4,
    map_mul, AlgHom.commutes]
  have h := divided_secant_relation (W.map (algebraMap R B)) q
    (algebraMap R B b3) (algebraMap R B b4) (algebraMap R B b6)
    (equation_map W s b3 b4 b6 a') (equation_map W s b3 b4 b6 c')
    (dividedSecantRefinement_denominator_isUnit W s b3 b4 b6 a c e)
    (dividedSecantRefinement_line W s b3 b4 b6 a c e)
  simp only [AlgHom.comp_apply, map_a₁, map_a₂] at h
  linear_combination q * h

/-- A regular scale lets the original line equation uniquely determine the divided slope. -/
theorem dividedSecantRefinement_eq_of_original_line (hs : IsRegular q) (z : B)
    (hz : z * (A x₀ - C x₀) = A y₀ - C y₀) : z = l := by
  have he := hz.trans
    (dividedSecantRefinement_original_line W s b3 b4 b6 a c h3 h4 h6 e).symm
  simp only [AlgHom.comp_apply, fromOriginal_x, map_mul, AlgHom.commutes] at he
  apply (dividedSecantRefinement_denominator_isUnit W s b3 b4 b6 a c e).mul_left_inj.mp
  apply hs.left
  simp only [AlgHom.comp_apply]
  linear_combination he

/-- The original output coordinates are functions of the original inputs and actual slope. -/
theorem dividedSecantRefinement_original_coord (i : Fin 3) :
    (e.comp (dividedSecantOutput W s b3 b4 b6 a c h3 h4 h6))
        (WeierstrassIntegralChart.coord W 2 i) =
      ![(W.map (algebraMap R B)).toAffine.addX (A x₀) (C x₀) l,
        (W.map (algebraMap R B)).toAffine.addY (A x₀) (C x₀) (A y₀) l, 1] i := by
  simp only [AlgHom.comp_apply, dividedSecantOutput,
    WeierstrassIntegralChart.evaluation_coord]
  fin_cases i <;>
    simp [dividedSecantX, dividedSecantY, fromOriginal_x, fromOriginal_y,
      Affine.addX, Affine.addY, Affine.negY, Affine.negAddY, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply R S T]

end FLT.Mazur.WeierstrassDilatation
