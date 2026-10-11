/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingCotangentCokernel
public import FLT.Mazur.TwoGeneratorRelationSequence
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Exactness and generic injectivity of the arithmetic cotangent relation

The explicit relation map presents completed original differentials.
In every algebra where the original parameter is a unit, its kernel vanishes.
This describes the relation matrix, without asserting a cotangent-homology comparison.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonSmoothing

variable {R : Type*} [CommRing R] (t : R) (S : Type*) [CommRing S]
  [Algebra (ChartRing t) S]

/-- The original arithmetic differential relation in a chart algebra. -/
def arithmeticCotangentRelation : S →ₗ[S] S × S :=
  TwoGeneratorRelation.relationMap (algebraMap (ChartRing t) S (leftCoordinate t))
    (algebraMap (ChartRing t) S (rightCoordinate t))

variable [Algebra R S] [IsScalarTower R (ChartRing t) S]

/-- The coefficients of the original differential relation multiply to the original parameter. -/
theorem arithmeticCotangentRelation_product :
    algebraMap (ChartRing t) S (leftCoordinate t) *
      algebraMap (ChartRing t) S (rightCoordinate t) = algebraMap R S t := by
  rw [← map_mul, coordinate_relation, ← IsScalarTower.algebraMap_apply]

/-- Inverting the original parameter kills the kernel of the explicit relation matrix. -/
theorem arithmeticCotangentRelation_ker_of_isUnit (ht : IsUnit (algebraMap R S t)) :
    LinearMap.ker (arithmeticCotangentRelation t S) = ⊥ := by
  apply TwoGeneratorRelation.ker_relationMap_of_isUnit_mul
  rwa [arithmeticCotangentRelation_product]

/-- Localization at the original parameter kills the kernel of the relation matrix. -/
theorem arithmeticCotangentRelation_ker_away
    [IsLocalization.Away (algebraMap R (ChartRing t) t) S] :
    LinearMap.ker (arithmeticCotangentRelation t S) = ⊥ :=
  arithmeticCotangentRelation_ker_of_isUnit t S (by
    rw [IsScalarTower.algebraMap_apply R (ChartRing t) S]
    exact IsLocalization.Away.algebraMap_isUnit (algebraMap R (ChartRing t) t))

variable [IsNoetherianRing (ChartRing t)] (I : Ideal (ChartRing t))

/-- The free-pair projection onto completed original differentials. -/
def completedCotangentProjection :
    (AdicCompletion I (ChartRing t) × AdicCompletion I (ChartRing t)) →ₗ[
      AdicCompletion I (ChartRing t)] AdicCompletion I Ω[ChartRing t⁄R] :=
  (completedCotangentCokernelEquiv t I).symm.toLinearMap.comp
    (TwoGeneratorRelation.relations
      (algebraMap (ChartRing t) (AdicCompletion I (ChartRing t)) (leftCoordinate t))
      (algebraMap (ChartRing t) (AdicCompletion I (ChartRing t)) (rightCoordinate t))).mkQ

/-- The completed cotangent projection is surjective. -/
theorem completedCotangentProjection_surjective :
    Function.Surjective (completedCotangentProjection t I) :=
  (completedCotangentCokernelEquiv t I).symm.surjective.comp (Submodule.mkQ_surjective _)

/-- The actual completed cotangent projection has exactly the original relation image as kernel. -/
theorem completedCotangentProjection_ker :
    LinearMap.ker (completedCotangentProjection t I) =
      LinearMap.range (arithmeticCotangentRelation t (AdicCompletion I (ChartRing t))) := by
  rw [completedCotangentProjection, LinearMap.ker_comp_of_ker_eq_bot _
    (LinearMap.ker_eq_bot.mpr (completedCotangentCokernelEquiv t I).symm.injective)]
  exact TwoGeneratorRelation.ker_projection _ _

end FLT.Mazur.PolygonSmoothing
