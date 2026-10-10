/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartParameterRecovery

/-!
# The quotient algebra attached to an explicit chart point

A named type for the actual tensor fiber keeps different parameter actions
separate. Its basis and ambient generators are inherited from the actual fiber.
-/

@[expose] public noncomputable section

open scoped BigOperators TensorProduct

namespace FLT.Mazur.HilbertChart

universe u v

variable (R : Type u) [CommRing R] (I : Type v) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)
variable {S : Type*} [CommRing S] [Algebra R S]
variable (f : ChartRing R I d w →ₐ[R] S)

/-- Cache the coefficient-ring instance for explicitly parametrized fibers. -/
local instance pointFamilyCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache the chart-ring instance for explicitly parametrized fibers. -/
local instance pointFamilyChartRing : CommRing (ChartRing R I d w) := inferInstance

/-- The chart-ring action of an explicit point. -/
abbrev pointScalars : Algebra (ChartRing R I d w) S := f.toRingHom.toAlgebra

/-- The explicit point action agrees with the original base-ring action. -/
theorem pointTower :
    let _ := pointScalars R I d w f
    IsScalarTower R (ChartRing R I d w) S := by
  let _ := pointScalars R I d w f
  exact IsScalarTower.of_algebraMap_eq fun r ↦ (f.commutes r).symm

/-- The actual tensor fiber, named to distinguish parameter actions in comparisons. -/
def PointFiber :=
  let _ := pointScalars R I d w f
  ChartFiber R I d w S

instance : CommRing (PointFiber R I d w f) :=
  @Algebra.TensorProduct.instCommRing (ChartRing R I d w) S (ChartAlgebra R I d w)
    _ _ (pointScalars R I d w f) _ _

instance : Algebra S (PointFiber R I d w f) :=
  @Algebra.TensorProduct.leftAlgebra (ChartRing R I d w) S S (ChartAlgebra R I d w)
    _ _ (pointScalars R I d w f) _ _ _ _ (by
      let _ := pointScalars R I d w f
      infer_instance)

instance : Algebra R (PointFiber R I d w f) := Algebra.compHom _ (algebraMap R S)

instance : IsScalarTower R S (PointFiber R I d w f) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The actual polynomial basis of the fiber at an explicit point. -/
def pointBasis : Module.Basis (Fin d) S (PointFiber R I d w f) :=
  @fiberBasis R _ I d w S _ (pointScalars R I d w f)

/-- The actual ambient generators of the fiber at an explicit point. -/
def pointGenerator (i : I) : PointFiber R I d w f :=
  @fiberGenerator R _ I d w S _ (pointScalars R I d w f) i

/-- The ambient quotient map over the test ring. -/
def pointEvaluation : MvPolynomial I S →ₐ[S] PointFiber R I d w f :=
  MvPolynomial.aeval (pointGenerator R I d w f)

/-- The prescribed original polynomials evaluate to the actual fiber basis. -/
theorem pointGenerator_basis (i : Fin d) :
    MvPolynomial.aeval (pointGenerator R I d w f) (w i) = pointBasis R I d w f i := by
  let _ := pointScalars R I d w f
  let _ := pointTower R I d w f
  exact fiberGenerator_basis R I d w S i

/-- Reading the fiber of an explicit point returns exactly that point. -/
theorem classifyingMap_point :
    classifyingMap R I d (pointBasis R I d w f) (pointGenerator R I d w f) w
      (pointGenerator_basis R I d w f) = f := by
  let _ := pointScalars R I d w f
  let _ := pointTower R I d w f
  exact classifyingMap_fiber R I d w S

/-- Extending original polynomial coefficients preserves evaluation. -/
theorem pointEvaluation_map (p : MvPolynomial I R) :
    pointEvaluation R I d w f (MvPolynomial.map (algebraMap R S) p) =
      MvPolynomial.aeval (pointGenerator R I d w f) p := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    simp only [MvPolynomial.map_C, pointEvaluation, MvPolynomial.aeval_C]
    rfl
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.map_X]
    rw [hp]
    simp only [pointEvaluation, MvPolynomial.aeval_X]

/-- The actual fiber evaluation is surjective because the prescribed images form its basis. -/
theorem pointEvaluation_surjective : Function.Surjective (pointEvaluation R I d w f) := by
  intro a
  refine ⟨∑ i, (pointBasis R I d w f).repr a i •
    MvPolynomial.map (algebraMap R S) (w i), ?_⟩
  simp only [map_sum, map_smul, pointEvaluation_map, pointGenerator_basis, Module.Basis.sum_repr]

end FLT.Mazur.HilbertChart
