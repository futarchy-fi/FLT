/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartFiberCoordinates

/-!
# Recovering parameters from the actual chart fiber

Extracting structure constants from a scalar extension recovers the original
parameter map. The prescribed polynomials are an actual basis in every fiber.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.HilbertChart

universe u v

variable (R : Type u) [CommRing R] (I : Type v) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)

/-- Cache the coefficient-ring instance for parameter recovery. -/
local instance parameterRecoveryCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache the chart-ring instance for parameter recovery. -/
local instance parameterRecoveryChartRing : CommRing (ChartRing R I d w) := inferInstance

variable (S : Type*) [CommRing S] [Algebra R S] [Algebra (ChartRing R I d w) S]
variable [IsScalarTower R (ChartRing R I d w) S]

/-- Cache the actual chart algebra ring before extracting its fiber coordinates. -/
local instance parameterRecoveryChartAlgebraRing : CommRing (ChartAlgebra R I d w) :=
  inferInstance
/-- Cache the actual fiber ring before extracting its coordinates. -/
local instance parameterRecoveryFiberRing : CommRing (ChartFiber R I d w S) := inferInstance

omit [Algebra (ChartRing R I d w) S] [IsScalarTower R (ChartRing R I d w) S] in
/-- A coefficient map is determined by multiplication, unit and generator values. -/
theorem coefficientMap_ext (f g : Coefficients R I d →ₐ[R] S)
    (hm : ∀ i j k, f (mulCoeff R I d i j k) = g (mulCoeff R I d i j k))
    (hu : ∀ k, f (unitCoeff R I d k) = g (unitCoeff R I d k))
    (hx : ∀ i k, f (generatorCoeff R I d i k) = g (generatorCoeff R I d i k)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro z
  cases z with
  | mul i j k => exact hm i j k
  | unit k => exact hu k
  | generator i k => exact hx i k

/-- Reading coefficients in the actual fiber recovers the coefficient parameter map. -/
theorem readCoefficients_fiber :
    readCoefficients R I d (A := ChartFiber R I d w S)
      (fiberBasis R I d w S) (fiberGenerator R I d w S) =
        (IsScalarTower.toAlgHom R (ChartRing R I d w) S).comp
          (Ideal.Quotient.mkₐ R (basisIdeal R I d w)) := by
  apply coefficientMap_ext
  · intro i j k
    rw [readCoefficients_mul, fiberBasis_mul]
    rfl
  · intro k
    rw [readCoefficients_unit, fiberBasis_unit]
    rfl
  · intro i k
    rw [readCoefficients_generator, fiberBasis_generator]
    rfl

/-- The original ambient evaluation commutes with passage to a chart fiber. -/
theorem fiberGenerator_evaluation (p : MvPolynomial I R) :
    MvPolynomial.aeval (fiberGenerator R I d w S) p =
      (1 : S) ⊗ₜ[ChartRing R I d w] chartInclusion R I d w (evaluation R I d p) := by
  let f : UniversalAlgebra R I d →ₐ[R] ChartFiber R I d w S :=
    (Algebra.TensorProduct.includeRight.restrictScalars R).comp
      ((chartInclusion R I d w).restrictScalars R)
  have h := MvPolynomial.comp_aeval_apply (B := ChartFiber R I d w S) (generator R I d) f p
  exact h.symm

/-- Every prescribed polynomial is the corresponding actual fiber basis vector. -/
theorem fiberGenerator_basis (i : Fin d) :
    MvPolynomial.aeval (fiberGenerator R I d w S) (w i) = fiberBasis R I d w S i := by
  rw [fiberGenerator_evaluation, chartInclusion_evaluation,
    fiberBasis, Module.Basis.baseChange_apply]

/-- Classifying the actual fiber recovers the original chart point. -/
theorem classifyingMap_fiber :
    classifyingMap R I d (A := ChartFiber R I d w S)
      (fiberBasis R I d w S) (fiberGenerator R I d w S) w
      (fiberGenerator_basis R I d w S) = IsScalarTower.toAlgHom R (ChartRing R I d w) S := by
  symm
  apply classifyingMap_unique
  intro a
  exact (AlgHom.congr_fun (readCoefficients_fiber R I d w S) a).symm

end FLT.Mazur.HilbertChart
