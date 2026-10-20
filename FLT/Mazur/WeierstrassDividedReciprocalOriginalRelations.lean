/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReciprocalSecantFormula

/-!
# Original-coordinate reciprocal relations

A regular divided scale lets the original line equation identify an inverse
slope. This works across different input depths and different source algebras.
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
  (e : DividedReciprocalRing W s b3 b4 b6 a c →ₐ[R] B)
local notation "T" => DividedReciprocalRing W s b3 b4 b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "a'" => (e.comp j).comp a
local notation "c'" => (e.comp j).comp c
local notation "orig" => fromOriginal W s b3 b4 b6 h3 h4 h6
local notation "A" => (a').comp orig
local notation "C" => (c').comp orig
local notation "x₀" => WeierstrassIntegralChart.coord W 2 0
local notation "y₀" => WeierstrassIntegralChart.coord W 2 1
local notation "l" => e (dividedReciprocalSlope W s b3 b4 b6 a c)
local notation "q" => algebraMap R B s

/-- The original ordinate difference is the scale times a unit. -/
theorem dividedReciprocalRefinement_original_difference (hs : IsRegular q) :
    IsRegular (A y₀ - C y₀) := by
  have hu := (dividedReciprocal_difference_isUnit W s b3 b4 b6 a c).map e
  have h : A y₀ - C y₀ = q *
      e (((j).comp a) (y W s b3 b4 b6) - ((j).comp c) (y W s b3 b4 b6)) := by
    simp only [AlgHom.comp_apply, fromOriginal_y, map_mul, map_sub, AlgHom.commutes]
    ring
  rw [h]
  exact hs.mul hu.isRegular

/-- The reciprocal relation also holds in the unchanged original coordinates. -/
theorem dividedReciprocalRefinement_original_line :
    l * (A y₀ - C y₀) = A x₀ - C x₀ := by
  have h := congrArg e (dividedReciprocalSlope_line W s b3 b4 b6 a c)
  simp only [AlgHom.comp_apply, map_mul, map_sub] at h
  simp only [AlgHom.comp_apply, fromOriginal_x, fromOriginal_y, map_mul, AlgHom.commutes]
  linear_combination q * h

/-- Any slope satisfying the original line equation is inverse to the reciprocal slope. -/
theorem dividedReciprocalRefinement_inverse_of_original_line (hs : IsRegular q) (z : B)
    (hz : z * (A x₀ - C x₀) = A y₀ - C y₀) : l * z = 1 := by
  apply (dividedReciprocalRefinement_original_difference
    W s b3 b4 b6 a c h3 h4 h6 e hs).right
  have h := dividedReciprocalRefinement_original_line W s b3 b4 b6 a c h3 h4 h6 e
  linear_combination z * h + hz

/-- The reciprocal homogeneous output depends only on the original inputs and actual slope. -/
theorem dividedReciprocalRefinement_original_coord (i : Fin 3) :
    e (dividedReciprocalCoordinates W s b3 b4 b6 a c i) =
      WeierstrassIntegralAddition.reciprocalXYZ (W.map (algebraMap R B))
        (A x₀) (C x₀) (A y₀) l i := by
  rw [dividedReciprocalRefinement_coordinates]
  simp only [AlgHom.comp_apply, fromOriginal_x, fromOriginal_y, map_mul, AlgHom.commutes]

end FLT.Mazur.WeierstrassDilatation
