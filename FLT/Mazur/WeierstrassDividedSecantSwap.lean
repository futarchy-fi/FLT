/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPairSecantEvaluation
public import FLT.Mazur.WeierstrassDividedSecantOriginalAction

/-!
# Symmetry of the universal divided secant

Swap the two full divided inputs by the universal localization property.
The divided line relation proves that the slope and original output are
unchanged, including over coefficient rings where the scale vanishes.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
local notation "P" => DividedPairRing W s b3 b4 b6
local notation "T" => DividedPairSecantRing W s b3 b4 b6
local notation "a" => dividedPairLeft W s b3 b4 b6
local notation "c" => dividedPairRight W s b3 b4 b6
local notation "j" => IsScalarTower.toAlgHom R P T
local notation "l" => dividedSecantSlope W s b3 b4 b6 a c

/-- The opposite ordered pair also has an invertible divided difference. -/
theorem dividedPairSecant_reverseDifference_isUnit :
    IsUnit (((j).comp c) (x W s b3 b4 b6) - ((j).comp a) (x W s b3 b4 b6)) := by
  have h := dividedSecantRefinement_difference_isUnit W s b3 b4 b6 a c (AlgHom.id R T)
  change IsUnit ((j) (a (x W s b3 b4 b6)) - (j) (c (x W s b3 b4 b6))) at h
  simpa only [neg_sub, AlgHom.comp_apply] using h.neg

/-- The actual swap map on the universal secant algebra. -/
def dividedPairSecantSwap : T →ₐ[R] T :=
  dividedPairSecantEvaluation W s b3 b4 b6 ((j).comp c) ((j).comp a)
    (dividedPairSecant_reverseDifference_isUnit W s b3 b4 b6)

/-- Swapping retains the full second input as its first input. -/
theorem dividedPairSecantSwap_left (z : Coordinate W s b3 b4 b6) :
    dividedPairSecantSwap W s b3 b4 b6 ((j) (a z)) = (j) (c z) :=
  dividedPairSecantEvaluation_left W s b3 b4 b6 _ _ _ z

/-- Swapping retains the full first input as its second input. -/
theorem dividedPairSecantSwap_right (z : Coordinate W s b3 b4 b6) :
    dividedPairSecantSwap W s b3 b4 b6 ((j) (c z)) = (j) (a z) :=
  dividedPairSecantEvaluation_right W s b3 b4 b6 _ _ _ z

/-- The slope is unchanged because both the numerator and denominator reverse sign. -/
theorem dividedPairSecantSwap_slope : dividedPairSecantSwap W s b3 b4 b6 l = l := by
  have hu := dividedSecantRefinement_difference_isUnit W s b3 b4 b6 a c (AlgHom.id R T)
  change IsUnit ((j) (a (x W s b3 b4 b6)) - (j) (c (x W s b3 b4 b6))) at hu
  apply hu.mul_left_inj.mp
  have h := congrArg (dividedPairSecantSwap W s b3 b4 b6)
    (dividedSecantSlope_relation W s b3 b4 b6 a c)
  simp only [map_mul, map_sub, AlgHom.comp_apply,
    dividedPairSecantSwap_left, dividedPairSecantSwap_right] at h
  have hl := dividedSecantSlope_relation W s b3 b4 b6 a c
  simp only [AlgHom.comp_apply] at hl
  linear_combination -h - hl

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

/-- The complete original output is symmetric without cancelling the original scale. -/
theorem dividedPairSecantSwap_output :
    (dividedPairSecantSwap W s b3 b4 b6).comp
        (dividedSecantOutput W s b3 b4 b6 a c h3 h4 h6) =
      dividedSecantOutput W s b3 b4 b6 a c h3 h4 h6 := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  simp only [AlgHom.comp_apply, dividedSecantOutput, WeierstrassIntegralChart.evaluation_coord]
  have hl := dividedSecantSlope_relation W s b3 b4 b6 a c
  simp only [AlgHom.comp_apply] at hl
  fin_cases i
  · change dividedPairSecantSwap W s b3 b4 b6 (dividedSecantX W s b3 b4 b6 a c) =
      dividedSecantX W s b3 b4 b6 a c
    simp only [dividedSecantX, Affine.addX, WeierstrassCurve.toAffine, map_a₁, map_a₂,
      map_sub, map_add, map_mul, map_pow, AlgHom.commutes, AlgHom.comp_apply,
      dividedPairSecantSwap_left, dividedPairSecantSwap_right, dividedPairSecantSwap_slope]
    ring
  · change dividedPairSecantSwap W s b3 b4 b6 (dividedSecantY W s b3 b4 b6 a c) =
      dividedSecantY W s b3 b4 b6 a c
    simp only [dividedSecantY, Affine.addY, WeierstrassCurve.toAffine,
      map_a₁, map_a₂, map_a₃,
      Affine.negY, Affine.negAddY, Affine.addX, map_sub, map_neg, map_add, map_mul,
      map_pow, AlgHom.commutes, AlgHom.comp_apply,
      dividedPairSecantSwap_left, dividedPairSecantSwap_right, dividedPairSecantSwap_slope]
    linear_combination -algebraMap R T s * hl
  · simp

/-- The spectrum swap retains the complete left input morphism. -/
@[reassoc] theorem dividedPairSecantSwap_spec_left :
    Spec.map (CommRingCat.ofHom (dividedPairSecantSwap W s b3 b4 b6).toRingHom) ≫
        Spec.map (CommRingCat.ofHom ((j).comp a).toRingHom) =
      Spec.map (CommRingCat.ofHom ((j).comp c).toRingHom) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact dividedPairSecantSwap_left W s b3 b4 b6 z

/-- The spectrum swap retains the complete right input morphism. -/
@[reassoc] theorem dividedPairSecantSwap_spec_right :
    Spec.map (CommRingCat.ofHom (dividedPairSecantSwap W s b3 b4 b6).toRingHom) ≫
        Spec.map (CommRingCat.ofHom ((j).comp c).toRingHom) =
      Spec.map (CommRingCat.ofHom ((j).comp a).toRingHom) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact dividedPairSecantSwap_right W s b3 b4 b6 z

/-- The actual original cubic output morphism is invariant under the swap. -/
@[reassoc] theorem dividedPairSecantSwap_toCurve :
    Spec.map (CommRingCat.ofHom (dividedPairSecantSwap W s b3 b4 b6).toRingHom) ≫
        dividedSecantToCurve W s b3 b4 b6 a c h3 h4 h6 =
      dividedSecantToCurve W s b3 b4 b6 a c h3 h4 h6 := by
  rw [dividedSecantToCurve, ← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((dividedPairSecantSwap W s b3 b4 b6).comp
    (dividedSecantOutput W s b3 b4 b6 a c h3 h4 h6)).toRingHom) ≫ _ = _
  rw [dividedPairSecantSwap_output]

end FLT.Mazur.WeierstrassDilatation
