/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentRelations

/-!
# Original-coordinate relations for divided tangent refinements

The slope satisfies the original line and chord equations at every divided
scale. A regular scale makes the original chord relation determine this slope,
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
  (e : DividedTangentRing W s b3 b4 b6 a c →ₐ[R] B)
local notation "T" => DividedTangentRing W s b3 b4 b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "a'" => (e.comp j).comp a
local notation "c'" => (e.comp j).comp c
local notation "orig" => fromOriginal W s b3 b4 b6 h3 h4 h6
local notation "A" => (a').comp orig
local notation "C" => (c').comp orig
local notation "x₀" => WeierstrassIntegralChart.coord W 2 0
local notation "y₀" => WeierstrassIntegralChart.coord W 2 1
local notation "l" => e (dividedTangentSlope W s b3 b4 b6 a c)
local notation "q" => algebraMap R B s

/-- The divided slope satisfies the line equation in the unchanged original coordinates. -/
theorem dividedTangentRefinement_original_line :
    l * (A x₀ - C x₀) = A y₀ - C y₀ := by
  simp only [AlgHom.comp_apply, fromOriginal_x, fromOriginal_y, map_mul, AlgHom.commutes]
  have h := dividedTangentRefinement_line W s b3 b4 b6 a c e
  simp only [AlgHom.comp_apply] at h
  linear_combination q * h

/-- The divided chord equation scales to the original cubic chord equation. -/
theorem dividedTangentRefinement_original_chord :
    l * (A y₀ + C y₀ + algebraMap R B W.a₁ * C x₀ + algebraMap R B W.a₃) =
      A x₀ ^ 2 + A x₀ * C x₀ + C x₀ ^ 2 +
        algebraMap R B W.a₂ * (A x₀ + C x₀) + algebraMap R B W.a₄ -
          algebraMap R B W.a₁ * A y₀ := by
  simp only [AlgHom.comp_apply, fromOriginal_x, fromOriginal_y, h3, h4,
    map_mul, AlgHom.commutes]
  have h := dividedTangentRefinement_chord W s b3 b4 b6 a c e
  simp only [AlgHom.comp_apply] at h
  linear_combination q * h

/-- A regular scale lets the original chord equation uniquely determine the divided slope. -/
theorem dividedTangentRefinement_eq_of_original_chord (hs : IsRegular q) (z : B)
    (hz : z * (A y₀ + C y₀ + algebraMap R B W.a₁ * C x₀ + algebraMap R B W.a₃) =
      A x₀ ^ 2 + A x₀ * C x₀ + C x₀ ^ 2 +
        algebraMap R B W.a₂ * (A x₀ + C x₀) + algebraMap R B W.a₄ -
          algebraMap R B W.a₁ * A y₀) : z = l := by
  have he := hz.trans
    (dividedTangentRefinement_original_chord W s b3 b4 b6 a c h3 h4 h6 e).symm
  simp only [AlgHom.comp_apply, fromOriginal_x, fromOriginal_y, h3,
    map_mul, AlgHom.commutes] at he
  apply (dividedTangentRefinement_denominator_isUnit W s b3 b4 b6 a c e).mul_left_inj.mp
  apply hs.left
  simp only [AlgHom.comp_apply]
  linear_combination he

/-- The original output coordinates are functions of the original inputs and actual slope. -/
theorem dividedTangentRefinement_original_coord (i : Fin 3) :
    (e.comp (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6))
        (WeierstrassIntegralChart.coord W 2 i) =
      ![(W.map (algebraMap R B)).toAffine.addX (A x₀) (C x₀) l,
        (W.map (algebraMap R B)).toAffine.addY (A x₀) (C x₀) (A y₀) l, 1] i := by
  simp only [AlgHom.comp_apply, dividedTangentOutput,
    WeierstrassIntegralChart.evaluation_coord]
  fin_cases i <;>
    simp [dividedTangentX, dividedTangentY, fromOriginal_x, fromOriginal_y,
      Affine.addX, Affine.addY, Affine.negY, Affine.negAddY, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply R S T]

end FLT.Mazur.WeierstrassDilatation
