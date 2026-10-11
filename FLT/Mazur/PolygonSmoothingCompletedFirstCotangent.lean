/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingFirstCotangentBaseChange
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# Completion of original arithmetic first cotangent homology

The completed original H1 is the kernel of the completed original relation
matrix. The finite-module completion comparison is applied to H1 itself.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonSmoothing

open TensorProduct

variable {R : Type*} [CommRing R] [IsDomain R] (t : R)
  [IsNoetherianRing (ChartRing t)] (I : Ideal (ChartRing t))

attribute [local irreducible] chartH1CotangentEquiv chartH1CotangentBaseChangeEquiv

/-- First cotangent homology of the original arithmetic chart is a finite module. -/
theorem chartH1Cotangent_finite : Module.Finite (ChartRing t)
    (Algebra.H1Cotangent R (ChartRing t)) :=
  Module.Finite.of_surjective (chartH1CotangentEquiv t).symm.toLinearMap
    (chartH1CotangentEquiv t).symm.surjective

/-- Completed original H1 is exactly the kernel of the completed original relation matrix. -/
def completedH1CotangentEquiv : AdicCompletion I (Algebra.H1Cotangent R (ChartRing t)) ≃ₗ[
    AdicCompletion I (ChartRing t)]
      LinearMap.ker (arithmeticCotangentRelation t (AdicCompletion I (ChartRing t))) := by
  let _ := chartH1Cotangent_finite t
  exact (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I
    (Algebra.H1Cotangent R (ChartRing t))).symm ≪≫ₗ
      chartH1CotangentBaseChangeEquiv t (AdicCompletion I (ChartRing t))

variable (S : Type*) [CommRing S] [Algebra (AdicCompletion I (ChartRing t)) S]
  [Module.Flat (AdicCompletion I (ChartRing t)) S]

/-- Flat extension of completed original H1 is the explicit relation kernel over the new ring. -/
def completedH1CotangentBaseChangeEquiv :
    S ⊗[AdicCompletion I (ChartRing t)]
      AdicCompletion I (Algebra.H1Cotangent R (ChartRing t)) ≃ₗ[S]
        LinearMap.ker (TwoGeneratorRelation.relationMap
          (algebraMap (AdicCompletion I (ChartRing t)) S
            (algebraMap (ChartRing t) (AdicCompletion I (ChartRing t)) (leftCoordinate t)))
          (algebraMap (AdicCompletion I (ChartRing t)) S
            (algebraMap (ChartRing t) (AdicCompletion I (ChartRing t)) (rightCoordinate t)))) :=
  (completedH1CotangentEquiv t I).baseChange _ S _ _ ≪≫ₗ
    TwoGeneratorRelation.relationKernelBaseChangeEquiv _ _ S

/-- Inverting the original parameter annihilates completed original first cotangent homology. -/
theorem completedH1CotangentBaseChange_subsingleton
    (ht : IsUnit (algebraMap (AdicCompletion I (ChartRing t)) S
      (algebraMap R (AdicCompletion I (ChartRing t)) t))) :
    Subsingleton (S ⊗[AdicCompletion I (ChartRing t)]
      AdicCompletion I (Algebra.H1Cotangent R (ChartRing t))) := by
  have hp := arithmeticCotangentRelation_product t (AdicCompletion I (ChartRing t))
  have hu := ht
  rw [← hp, map_mul] at hu
  let _ : Subsingleton (LinearMap.ker (TwoGeneratorRelation.relationMap
      (algebraMap (AdicCompletion I (ChartRing t)) S
        (algebraMap (ChartRing t) (AdicCompletion I (ChartRing t)) (leftCoordinate t)))
      (algebraMap (AdicCompletion I (ChartRing t)) S
        (algebraMap (ChartRing t) (AdicCompletion I (ChartRing t)) (rightCoordinate t))))) :=
    Submodule.subsingleton_iff_eq_bot.mpr
      (TwoGeneratorRelation.ker_relationMap_of_isUnit_mul _ _ hu)
  exact (completedH1CotangentBaseChangeEquiv t I S).subsingleton

/-- Localization at the original parameter kills the completion of original H1. -/
theorem completedH1CotangentBaseChange_away
    [IsLocalization.Away (algebraMap R (AdicCompletion I (ChartRing t)) t) S] :
    Subsingleton (S ⊗[AdicCompletion I (ChartRing t)]
      AdicCompletion I (Algebra.H1Cotangent R (ChartRing t))) :=
  completedH1CotangentBaseChange_subsingleton t I S
    (IsLocalization.Away.algebraMap_isUnit (algebraMap R (AdicCompletion I (ChartRing t)) t))

end FLT.Mazur.PolygonSmoothing
