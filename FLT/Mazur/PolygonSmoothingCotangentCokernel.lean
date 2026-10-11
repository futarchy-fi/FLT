/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingCompletedDifferentials
public import FLT.Mazur.TwoGeneratorRelationQuotient

/-!
# An explicit cokernel for completed original arithmetic differentials

The completion of the original differential module of xy=t is the quotient
of two copies of the completed ring by the original coordinate relation.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] (t : R) [IsNoetherianRing (ChartRing t)]
  (I : Ideal (ChartRing t))

/-- The completed original first coordinate differential. -/
def completedLeftDifferential : AdicCompletion I Ω[ChartRing t⁄R] :=
  AdicCompletion.of I Ω[ChartRing t⁄R] (KaehlerDifferential.D R _ (leftCoordinate t))

/-- The completed original second coordinate differential. -/
def completedRightDifferential : AdicCompletion I Ω[ChartRing t⁄R] :=
  AdicCompletion.of I Ω[ChartRing t⁄R] (KaehlerDifferential.D R _ (rightCoordinate t))

/-- The explicit one-relation cokernel over the completed arithmetic ring. -/
abbrev CompletedCotangentCokernel :=
  TwoGeneratorRelation.Model
    (algebraMap (ChartRing t) (AdicCompletion I (ChartRing t)) (leftCoordinate t))
    (algebraMap (ChartRing t) (AdicCompletion I (ChartRing t)) (rightCoordinate t))

omit [IsNoetherianRing (ChartRing t)] in
/-- The original differential relation survives completion with its original coefficients. -/
theorem completedDifferential_relation :
    algebraMap (ChartRing t) (AdicCompletion I (ChartRing t)) (leftCoordinate t) •
        completedRightDifferential t I +
      algebraMap (ChartRing t) (AdicCompletion I (ChartRing t)) (rightCoordinate t) •
        completedLeftDifferential t I = 0 := by
  rw [algebraMap_smul, algebraMap_smul]
  exact congrArg (AdicCompletion.of I Ω[ChartRing t⁄R])
    (derivation_coordinate_relation t (KaehlerDifferential.D R (ChartRing t)))

/-- Send the two cokernel generators to the actual completed original differentials. -/
def completedCokernelToDifferentials : CompletedCotangentCokernel t I →ₗ[
    AdicCompletion I (ChartRing t)] AdicCompletion I Ω[ChartRing t⁄R] :=
  TwoGeneratorRelation.lift _ _ (completedLeftDifferential t I)
    (completedRightDifferential t I) (completedDifferential_relation t I)

/-- Send actual completed original differentials to the explicit quotient presentation. -/
def completedDifferentialsToCokernel : AdicCompletion I Ω[ChartRing t⁄R] →ₗ[
    AdicCompletion I (ChartRing t)] CompletedCotangentCokernel t I :=
  completedDifferentialLift t I (TwoGeneratorRelation.left _ _)
    (TwoGeneratorRelation.right _ _) (by
      rw [← algebraMap_smul (AdicCompletion I (ChartRing t)) (leftCoordinate t),
        ← algebraMap_smul (AdicCompletion I (ChartRing t)) (rightCoordinate t)]
      exact TwoGeneratorRelation.relation _ _)

/-- The cokernel and completed differential comparison is inverse on actual differentials. -/
theorem completedCokernelToDifferentials_comp :
    (completedCokernelToDifferentials t I).comp (completedDifferentialsToCokernel t I) =
      LinearMap.id := by
  apply completedDifferential_ext t I
  · change completedCokernelToDifferentials t I
      (completedDifferentialsToCokernel t I (completedLeftDifferential t I)) = _
    simp [completedDifferentialsToCokernel, completedLeftDifferential,
      completedCokernelToDifferentials]
  · change completedCokernelToDifferentials t I
      (completedDifferentialsToCokernel t I (completedRightDifferential t I)) = _
    simp [completedDifferentialsToCokernel, completedRightDifferential,
      completedCokernelToDifferentials]

/-- The completed differential and cokernel comparison is inverse on the explicit quotient. -/
theorem completedDifferentialsToCokernel_comp :
    (completedDifferentialsToCokernel t I).comp (completedCokernelToDifferentials t I) =
      LinearMap.id := by
  apply TwoGeneratorRelation.hom_ext
  · simp [LinearMap.comp_apply, completedCokernelToDifferentials,
      completedDifferentialsToCokernel, completedLeftDifferential]
  · simp [LinearMap.comp_apply, completedCokernelToDifferentials,
      completedDifferentialsToCokernel, completedRightDifferential]

/-- Completed original arithmetic differentials are the explicit one-relation cokernel. -/
def completedCotangentCokernelEquiv : AdicCompletion I Ω[ChartRing t⁄R] ≃ₗ[
    AdicCompletion I (ChartRing t)] CompletedCotangentCokernel t I :=
  { completedDifferentialsToCokernel t I with
    invFun := completedCokernelToDifferentials t I
    left_inv := LinearMap.congr_fun (completedCokernelToDifferentials_comp t I)
    right_inv := LinearMap.congr_fun (completedDifferentialsToCokernel_comp t I) }

end FLT.Mazur.PolygonSmoothing
