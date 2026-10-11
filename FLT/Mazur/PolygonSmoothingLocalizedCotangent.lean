/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingCotangentCokernel
public import FLT.Mazur.TwoGeneratorRelationBaseChange
public import FLT.Mazur.TwoGeneratorRelationUnit
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Original completed cotangent modules after inverting the original parameter

The explicit presentation commutes with arbitrary scalar extension.
After inverting the image of the original smoothing parameter, the
scalar extension of completed original differentials is free of rank one.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.PolygonSmoothing

variable {R : Type*} [CommRing R] (t : R) [IsNoetherianRing (ChartRing t)]
  (I : Ideal (ChartRing t)) (S : Type*) [CommRing S]
  [Algebra (AdicCompletion I (ChartRing t)) S]

/-- The completed original arithmetic cotangent presentation commutes with scalar extension. -/
def completedCotangentBaseChangeEquiv :
    S ⊗[AdicCompletion I (ChartRing t)] AdicCompletion I Ω[ChartRing t⁄R] ≃ₗ[S]
      TwoGeneratorRelation.Model
        (algebraMap (AdicCompletion I (ChartRing t)) S
          (algebraMap (ChartRing t) (AdicCompletion I (ChartRing t)) (leftCoordinate t)))
        (algebraMap (AdicCompletion I (ChartRing t)) S
          (algebraMap (ChartRing t) (AdicCompletion I (ChartRing t)) (rightCoordinate t))) :=
  ((completedCotangentCokernelEquiv t I).baseChange _ S _ _).trans
    (TwoGeneratorRelation.baseChangeEquiv _ _ S)

omit [IsNoetherianRing (ChartRing t)] in
/-- The left coefficient is a unit wherever the original parameter becomes a unit. -/
theorem completedLeftCoordinate_isUnit
    (ht : IsUnit (algebraMap (AdicCompletion I (ChartRing t)) S
      (algebraMap R (AdicCompletion I (ChartRing t)) t))) :
    IsUnit (algebraMap (AdicCompletion I (ChartRing t)) S
      (algebraMap (ChartRing t) (AdicCompletion I (ChartRing t)) (leftCoordinate t))) := by
  have hp :
      algebraMap (ChartRing t) (AdicCompletion I (ChartRing t)) (leftCoordinate t) *
        algebraMap (ChartRing t) (AdicCompletion I (ChartRing t)) (rightCoordinate t) =
          algebraMap R (AdicCompletion I (ChartRing t)) t := by
    rw [← map_mul, coordinate_relation, ← IsScalarTower.algebraMap_apply]
  have hu := ht
  rw [← hp, map_mul] at hu
  exact (IsUnit.mul_iff.mp hu).1

/-- Making the original parameter a unit makes completed original differentials rank one. -/
def completedCotangentUnitEquiv
    (ht : IsUnit (algebraMap (AdicCompletion I (ChartRing t)) S
      (algebraMap R (AdicCompletion I (ChartRing t)) t))) :
    S ⊗[AdicCompletion I (ChartRing t)] AdicCompletion I Ω[ChartRing t⁄R] ≃ₗ[S] S :=
  (completedCotangentBaseChangeEquiv t I S).trans
    (TwoGeneratorRelation.ofIsUnitEquiv _ _ (completedLeftCoordinate_isUnit t I S ht))

/-- Inverting the original parameter gives an explicit rank-one cotangent equivalence. -/
def completedCotangentLocalizedEquiv
    [IsLocalization.Away (algebraMap R (AdicCompletion I (ChartRing t)) t) S] :
    S ⊗[AdicCompletion I (ChartRing t)] AdicCompletion I Ω[ChartRing t⁄R] ≃ₗ[S] S :=
  completedCotangentUnitEquiv t I S
    (IsLocalization.Away.algebraMap_isUnit (algebraMap R (AdicCompletion I (ChartRing t)) t))

end FLT.Mazur.PolygonSmoothing
