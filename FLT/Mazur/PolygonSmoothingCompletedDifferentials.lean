/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicDerivationExtension
public import FLT.Mazur.PolygonSmoothingDerivation

/-!
# The completed arithmetic cotangent presentation

The two original coordinate differentials generate completed original
differentials. Their single relation describes maps into every module over
the completed ring. Derivations on the completed chart satisfy the same
presentation when the target is separated for the original ideal.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

variable {R N : Type*} [CommRing R] (t : R) [IsNoetherianRing (ChartRing t)]
  (I : Ideal (ChartRing t)) [AddCommGroup N] [Module R N]
  [Module (ChartRing t) N] [IsScalarTower R (ChartRing t) N]
  [Module (AdicCompletion I (ChartRing t)) N]
  [IsScalarTower (ChartRing t) (AdicCompletion I (ChartRing t)) N]
  [Module (MvPolynomial (Fin 2) R) N]
  [IsScalarTower R (MvPolynomial (Fin 2) R) N]
  [IsScalarTower (MvPolynomial (Fin 2) R) (ChartRing t) N]

/-- A solution of the original cotangent relation defines a map on completed differentials. -/
def completedDifferentialLift (u v : N)
    (huv : leftCoordinate t • v + rightCoordinate t • u = 0) :
    AdicCompletion I Ω[ChartRing t⁄R] →ₗ[AdicCompletion I (ChartRing t)] N :=
  AdicFiniteModuleLift.lift I (derivationOfCoordinates t u v huv).liftKaehlerDifferential

/-- The factorization retains the original first coordinate differential. -/
@[simp] theorem completedDifferentialLift_left (u v : N)
    (huv : leftCoordinate t • v + rightCoordinate t • u = 0) :
    completedDifferentialLift t I u v huv
      (AdicCompletion.of I Ω[ChartRing t⁄R] (KaehlerDifferential.D R _ (leftCoordinate t))) =
        u := by
  rw [completedDifferentialLift, AdicFiniteModuleLift.lift_of,
    Derivation.liftKaehlerDifferential_comp_D, derivationOfCoordinates_left]

/-- The factorization retains the original second coordinate differential. -/
@[simp] theorem completedDifferentialLift_right (u v : N)
    (huv : leftCoordinate t • v + rightCoordinate t • u = 0) :
    completedDifferentialLift t I u v huv
      (AdicCompletion.of I Ω[ChartRing t⁄R] (KaehlerDifferential.D R _ (rightCoordinate t))) =
        v := by
  rw [completedDifferentialLift, AdicFiniteModuleLift.lift_of,
    Derivation.liftKaehlerDifferential_comp_D, derivationOfCoordinates_right]

omit [IsNoetherianRing (ChartRing t)]
  [IsScalarTower R (MvPolynomial (Fin 2) R) N] in
/-- The two original coordinate differentials determine a completed-linear map. -/
theorem completedDifferential_ext
    (f g : AdicCompletion I Ω[ChartRing t⁄R] →ₗ[AdicCompletion I (ChartRing t)] N)
    (hx : f (AdicCompletion.of I Ω[ChartRing t⁄R]
      (KaehlerDifferential.D R _ (leftCoordinate t))) =
        g (AdicCompletion.of I Ω[ChartRing t⁄R]
          (KaehlerDifferential.D R _ (leftCoordinate t))))
    (hy : f (AdicCompletion.of I Ω[ChartRing t⁄R]
      (KaehlerDifferential.D R _ (rightCoordinate t))) =
        g (AdicCompletion.of I Ω[ChartRing t⁄R]
          (KaehlerDifferential.D R _ (rightCoordinate t)))) : f = g := by
  apply AdicFiniteModuleExt.ext_of I
  have he : (f.restrictScalars (ChartRing t)).comp (AdicCompletion.of I Ω[ChartRing t⁄R]) =
      (g.restrictScalars (ChartRing t)).comp (AdicCompletion.of I Ω[ChartRing t⁄R]) := by
    apply Derivation.liftKaehlerDifferential_unique
    exact chartRing_derivation_ext t _ _ hx hy
  exact fun m ↦ LinearMap.congr_fun he m

/-- Every prescribed solution of the cotangent relation has a unique completed-linear lift. -/
theorem completedDifferentialLift_unique (u v : N)
    (huv : leftCoordinate t • v + rightCoordinate t • u = 0)
    (f : AdicCompletion I Ω[ChartRing t⁄R] →ₗ[AdicCompletion I (ChartRing t)] N)
    (hx : f (AdicCompletion.of I Ω[ChartRing t⁄R]
      (KaehlerDifferential.D R _ (leftCoordinate t))) = u)
    (hy : f (AdicCompletion.of I Ω[ChartRing t⁄R]
      (KaehlerDifferential.D R _ (rightCoordinate t))) = v) :
    f = completedDifferentialLift t I u v huv := by
  apply completedDifferential_ext t I
  · rw [completedDifferentialLift_left, hx]
  · rw [completedDifferentialLift_right, hy]

variable [IsScalarTower R (AdicCompletion I (ChartRing t)) N]

/-- The completed arithmetic chart has the same derivation presentation in separated targets. -/
def completedDerivationCoordinateEquiv [IsHausdorff I N] :
    Derivation R (AdicCompletion I (ChartRing t)) N ≃
      {p : N × N // leftCoordinate t • p.2 + rightCoordinate t • p.1 = 0} :=
  (AdicDerivationExtension.equiv I).symm.trans (derivationCoordinateEquiv t)

end FLT.Mazur.PolygonSmoothing
