/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralChart
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# A regular reciprocal of x near source infinity

In the chart Y = 1 the cubic reads v H = u³, where H has value one
at infinity. On D(H), u²/H is regular and its product with u is v.
-/

@[expose] public noncomputable section

open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

variable {K : Type} [Field K] (E : WeierstrassCurve K)

/-- The factor multiplying v in the equation of the infinity chart. -/
def infinityFactor : Coordinate E 1 :=
  1 + algebraMap K _ E.a₁ * coord E 1 0 + algebraMap K _ E.a₃ * coord E 1 2 -
    algebraMap K _ E.a₂ * coord E 1 0 ^ 2 -
    algebraMap K _ E.a₄ * coord E 1 0 * coord E 1 2 -
    algebraMap K _ E.a₆ * coord E 1 2 ^ 2

/-- The original cubic supplies the divisibility needed for a regular reciprocal. -/
theorem infinityFactor_relation :
    coord E 1 2 * infinityFactor E = coord E 1 0 ^ 3 := by
  have h := (Projective.equation_iff _).mp (coord_equation E 1)
  simp only [coord_self, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, one_pow,
    one_mul, mul_one] at h
  unfold infinityFactor
  linear_combination h

/-- Evaluation of the actual source infinity chart at the original identity. -/
def infinityEvaluation : Coordinate E 1 →ₐ[K] K :=
  evaluation E 1 ![0, 1, 0] Projective.equation_zero rfl

@[simp] theorem infinityEvaluation_u : infinityEvaluation E (coord E 1 0) = 0 :=
  evaluation_coord _ _ _ _ _ _

@[simp] theorem infinityEvaluation_v : infinityEvaluation E (coord E 1 2) = 0 :=
  evaluation_coord _ _ _ _ _ _

/-- The neighborhood D(H) contains the original infinity point. -/
@[simp] theorem infinityEvaluation_factor : infinityEvaluation E (infinityFactor E) = 1 := by
  simp [infinityFactor]

/-- The factor being inverted is an actual nonzero chart function. -/
theorem infinityFactor_ne_zero : infinityFactor E ≠ 0 := by
  intro h
  have := congrArg (infinityEvaluation E) h
  simp at this

/-- The first explicit affine neighborhood of source infinity. -/
abbrev InfinityParameterRing := Localization.Away (infinityFactor E)

/-- The original infinity point lifts to this principal localization. -/
def infinityParameterEvaluation : InfinityParameterRing E →ₐ[K] K :=
  IsLocalization.Away.liftAlgHom (infinityFactor E)
    (show IsUnit (infinityEvaluation E (infinityFactor E)) by simp)

@[simp] theorem infinityParameterEvaluation_algebraMap (a : Coordinate E 1) :
    infinityParameterEvaluation E (algebraMap _ (InfinityParameterRing E) a) =
      infinityEvaluation E a :=
  IsLocalization.Away.lift_eq _
    (show IsUnit (infinityEvaluation E (infinityFactor E)) by simp) a

/-- A regular representative of the reciprocal affine x-coordinate. -/
def infinityReciprocal : InfinityParameterRing E :=
  algebraMap _ _ (coord E 1 0) ^ 2 * IsLocalization.Away.invSelf (infinityFactor E)

/-- The original coordinate relation holds without dividing by the vanishing u. -/
theorem infinityReciprocal_relation :
    algebraMap _ (InfinityParameterRing E) (coord E 1 0) * infinityReciprocal E =
      algebraMap _ _ (coord E 1 2) := by
  have h := congrArg (algebraMap _ (InfinityParameterRing E)) (infinityFactor_relation E)
  simp only [map_mul, map_pow] at h
  calc
    _ = algebraMap _ (InfinityParameterRing E) (coord E 1 0) ^ 3 *
        IsLocalization.Away.invSelf (infinityFactor E) := by unfold infinityReciprocal; ring
    _ = _ := by rw [← h, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]

/-- The reciprocal vanishes at the original point at infinity. -/
@[simp] theorem infinityParameterEvaluation_reciprocal :
    infinityParameterEvaluation E (infinityReciprocal E) = 0 := by
  simp [infinityReciprocal]

end WeierstrassCurve.Velu
