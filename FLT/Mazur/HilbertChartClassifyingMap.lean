/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartAlgebraRealization
public import FLT.Mazur.HilbertChartBasisRelations

/-!
# The parameter map to a prescribed-basis Hilbert chart

For an arbitrary based algebra whose prescribed polynomials evaluate to its basis,
the extracted coefficient map factors through the actual closed basis chart.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.HilbertChart

universe u v

variable (R : Type u) [CommRing R] (I : Type v) (d : ℕ)

/-- The distinguished universal basis has the original vector coordinates. -/
theorem basis_repr_coordinates (a : UniversalAlgebra R I d) (k : Fin d) :
    (basis R I d).repr a k = coordinates R I d a k := by
  change (Pi.basisFun (Coefficients R I d) (Fin d)).repr a k = a k
  exact Pi.basisFun_repr (R := Coefficients R I d) (η := Fin d) a k

variable {S A : Type*} [CommRing S] [CommRing A] [Algebra R S] [Algebra S A]
variable [Algebra R A] [IsScalarTower R S A]
variable (v : Module.Basis (Fin d) S A) (x : I → A)
variable (w : Fin d → MvPolynomial I R)
variable (hw : ∀ i, MvPolynomial.aeval x (w i) = v i)

include hw

/-- The extracted coefficient map sends prescribed polynomial coordinates to deltas. -/
theorem readCoefficients_basis_equations (i k : Fin d) :
    readCoefficients R I d v x ((basis R I d).repr (evaluation R I d (w i)) k) =
      if i = k then 1 else 0 := by
  rw [basis_repr_coordinates]
  have h := realizeVector_repr R I d v x (evaluation R I d (w i)) k
  change v.repr (realization R I d v x (evaluation R I d (w i))) k = _ at h
  rw [realization_evaluation, hw, Module.Basis.repr_self_apply] at h
  exact h.symm

/-- The extracted coefficient map kills the actual prescribed-basis ideal. -/
theorem basisIdeal_le_readCoefficients_ker :
    basisIdeal R I d w ≤ RingHom.ker (readCoefficients R I d v x).toRingHom :=
  (basisIdeal_le_ker_iff R I d w _).mpr (readCoefficients_basis_equations R I d v x w hw)

/-- The actual parameter map from the prescribed-basis chart ring to the test ring. -/
def classifyingMap : ChartRing R I d w →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (readCoefficients R I d v x)
    (basisIdeal_le_readCoefficients_ker R I d v x w hw)

/-- The chart-ring parameter map lifts the extracted universal coefficient map. -/
theorem classifyingMap_chartMap (a : Coefficients R I d) :
    classifyingMap R I d v x w hw (chartMap R I d w a) = readCoefficients R I d v x a := rfl

/-- A map out of the basis chart is uniquely determined by its coefficient values. -/
theorem classifyingMap_unique (f : ChartRing R I d w →ₐ[R] S)
    (hf : ∀ a, f (chartMap R I d w a) = readCoefficients R I d v x a) :
    f = classifyingMap R I d v x w hw := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro a
  exact hf a

end FLT.Mazur.HilbertChart
