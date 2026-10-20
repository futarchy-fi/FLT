/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecantSchemeAction
public import FLT.Mazur.WeierstrassDividedSecantOriginalAction

/-!
# Reversing arbitrary supplied divided secant inputs

The opposite secant localization maps into the original one. Its slope and
complete original output are unchanged without inverting the chart scale.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "T" => DividedSecantRing W s b3 b4 b6 a c
local notation "V" => DividedSecantRing W s b3 b4 b6 c a
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "v" => IsScalarTower.toAlgHom R S V
local notation "l" => dividedSecantSlope W s b3 b4 b6 a c

/-- The reverse divided difference is a unit on the original secant localization. -/
theorem dividedSecant_reverseDifference_isUnit :
    IsUnit ((j) (c (x W s b3 b4 b6) - a (x W s b3 b4 b6))) := by
  have h : IsUnit ((j) (a (x W s b3 b4 b6) - c (x W s b3 b4 b6))) :=
    IsLocalization.Away.algebraMap_isUnit _
  simpa only [← map_neg, neg_sub] using h.neg

/-- The reverse secant is evaluated through the same source algebra map. -/
def dividedSecantReverse : V →ₐ[R] T :=
  IsLocalization.Away.liftAlgHom (c (x W s b3 b4 b6) - a (x W s b3 b4 b6))
    (f := j) (dividedSecant_reverseDifference_isUnit W s b3 b4 b6 a c)

/-- Reversal preserves every element from the unchanged source algebra. -/
theorem dividedSecantReverse_base (z : S) :
    dividedSecantReverse W s b3 b4 b6 a c ((v) z) = (j) z := by
  simp only [dividedSecantReverse, IsLocalization.Away.coe_liftAlgHom,
    IsScalarTower.toAlgHom_apply, IsLocalization.Away.lift_eq,
    AlgHom.toRingHom_eq_coe, IsScalarTower.coe_toAlgHom]

/-- Both signs reverse in the secant slope. -/
theorem dividedSecantReverse_slope :
    dividedSecantReverse W s b3 b4 b6 a c (dividedSecantSlope W s b3 b4 b6 c a) = l := by
  have hu : IsUnit ((j) (a (x W s b3 b4 b6)) - (j) (c (x W s b3 b4 b6))) := by
    simpa only [map_sub, IsScalarTower.toAlgHom_apply] using
      (IsLocalization.Away.algebraMap_isUnit
        (a (x W s b3 b4 b6) - c (x W s b3 b4 b6)) (S := T))
  apply hu.mul_left_inj.mp
  have h := congrArg (dividedSecantReverse W s b3 b4 b6 a c)
    (dividedSecantSlope_relation W s b3 b4 b6 c a)
  simp only [map_mul, map_sub, AlgHom.comp_apply, dividedSecantReverse_base] at h
  have hl := dividedSecantSlope_relation W s b3 b4 b6 a c
  simp only [AlgHom.comp_apply] at hl
  linear_combination -h - hl

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

/-- The complete original output is symmetric without cancelling the original scale. -/
theorem dividedSecantReverse_output :
    (dividedSecantReverse W s b3 b4 b6 a c).comp
        (dividedSecantOutput W s b3 b4 b6 c a h3 h4 h6) =
      dividedSecantOutput W s b3 b4 b6 a c h3 h4 h6 := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  simp only [AlgHom.comp_apply, dividedSecantOutput, WeierstrassIntegralChart.evaluation_coord]
  have hl := dividedSecantSlope_relation W s b3 b4 b6 a c
  simp only [AlgHom.comp_apply] at hl
  fin_cases i
  · change dividedSecantReverse W s b3 b4 b6 a c (dividedSecantX W s b3 b4 b6 c a) =
      dividedSecantX W s b3 b4 b6 a c
    simp only [dividedSecantX, Affine.addX, WeierstrassCurve.toAffine, map_a₁, map_a₂,
      map_sub, map_add, map_mul, map_pow, AlgHom.commutes, AlgHom.comp_apply,
      dividedSecantReverse_base, dividedSecantReverse_slope]
    ring
  · change dividedSecantReverse W s b3 b4 b6 a c (dividedSecantY W s b3 b4 b6 c a) =
      dividedSecantY W s b3 b4 b6 a c
    simp only [dividedSecantY, Affine.addY, WeierstrassCurve.toAffine,
      map_a₁, map_a₂, map_a₃,
      Affine.negY, Affine.negAddY, Affine.addX, map_sub, map_neg, map_add, map_mul,
      map_pow, AlgHom.commutes, AlgHom.comp_apply,
      dividedSecantReverse_base, dividedSecantReverse_slope]
    linear_combination -algebraMap R T s * hl
  · simp

/-- The reversed spectrum map preserves the complete input map from the source algebra. -/
@[reassoc] theorem dividedSecantReverse_spec_base :
    Spec.map (CommRingCat.ofHom (dividedSecantReverse W s b3 b4 b6 a c).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (v).toRingHom) =
      Spec.map (CommRingCat.ofHom (j).toRingHom) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact dividedSecantReverse_base W s b3 b4 b6 a c

/-- The original cubic output is unchanged by reversal of the supplied secant. -/
@[reassoc] theorem dividedSecantReverse_toCurve :
    Spec.map (CommRingCat.ofHom (dividedSecantReverse W s b3 b4 b6 a c).toRingHom) ≫
        dividedSecantToCurve W s b3 b4 b6 c a h3 h4 h6 =
      dividedSecantToCurve W s b3 b4 b6 a c h3 h4 h6 := by
  rw [dividedSecantToCurve, ← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((dividedSecantReverse W s b3 b4 b6 a c).comp
    (dividedSecantOutput W s b3 b4 b6 c a h3 h4 h6)).toRingHom) ≫ _ = _
  rw [dividedSecantReverse_output]
  rfl

end FLT.Mazur.WeierstrassDilatation
