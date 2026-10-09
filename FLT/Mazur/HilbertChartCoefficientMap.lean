/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartStructureConstants
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Reading a coefficient map from an arbitrary based algebra

An actual basis and ambient generator vectors determine an algebra map from
the ring-law quotient. Its existence follows from the proved coordinate equations.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.HilbertChart

universe u v

variable (R : Type u) [CommRing R] (I : Type v) (d : ℕ)
variable {S A : Type*} [CommRing S] [CommRing A] [Algebra R S] [Algebra S A]
variable (v : Module.Basis (Fin d) S A) (x : I → A)

/-- Read all polynomial parameter coordinates in an actual based algebra. -/
def parameterValues : Variable I d → S
  | .mul i j k => structureCoeff v i j k
  | .unit k => structureUnit v k
  | .generator i k => v.repr (x i) k

/-- Evaluation of the parameter polynomial ring in the actual coefficient ring. -/
def readParameters : Parameters R I d →ₐ[R] S :=
  MvPolynomial.aeval (parameterValues I d v x)

/-- The actual structure constants kill every defining ring-law equation. -/
theorem readParameters_equation (e : Equation d) :
    readParameters R I d v x (equation R I d e) = 0 := by
  cases e with
  | comm i j k =>
    simp only [equation, map_sub, readParameters, mulVar, MvPolynomial.aeval_X,
      parameterValues, structureCoeff_comm v i j k, sub_self]
  | assoc i j k l =>
    simp only [equation, map_sub, map_sum, map_mul, readParameters, mulVar,
      MvPolynomial.aeval_X, parameterValues, structureCoeff_assoc v i j k l, sub_self]
  | unit i k =>
    simp only [equation, map_sub, map_sum, map_mul, readParameters, mulVar, unitVar,
      MvPolynomial.aeval_X, parameterValues, structureUnit_mul]
    split_ifs <;> simp only [map_one, map_zero, sub_self]

/-- The equation ideal is contained in the kernel of the actual parameter evaluation. -/
theorem equationIdeal_le_readParameters_ker :
    equationIdeal R I d ≤ RingHom.ker (readParameters R I d v x).toRingHom := by
  rw [equationIdeal, Ideal.span_le]
  rintro _ ⟨e, rfl⟩
  exact readParameters_equation R I d v x e

/-- The induced coefficient map from the actual universal ring-law quotient. -/
def readCoefficients : Coefficients R I d →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (readParameters R I d v x)
    (equationIdeal_le_readParameters_ker R I d v x)

/-- The classifying coefficient map recovers each actual multiplication coefficient. -/
theorem readCoefficients_mul (i j k : Fin d) :
    readCoefficients R I d v x (mulCoeff R I d i j k) = structureCoeff v i j k := by
  change MvPolynomial.aeval (parameterValues I d v x)
    (MvPolynomial.X (Variable.mul i j k)) = _
  exact MvPolynomial.aeval_X _ _

/-- The classifying coefficient map recovers the actual unit coordinates. -/
theorem readCoefficients_unit (k : Fin d) :
    readCoefficients R I d v x (unitCoeff R I d k) = structureUnit v k := by
  change MvPolynomial.aeval (parameterValues I d v x)
    (MvPolynomial.X (Variable.unit k)) = _
  exact MvPolynomial.aeval_X _ _

/-- The classifying coefficient map recovers the actual ambient generator coordinates. -/
theorem readCoefficients_generator (i : I) (k : Fin d) :
    readCoefficients R I d v x (generatorCoeff R I d i k) = v.repr (x i) k := by
  change MvPolynomial.aeval (parameterValues I d v x)
    (MvPolynomial.X (Variable.generator i k)) = _
  exact MvPolynomial.aeval_X _ _

end FLT.Mazur.HilbertChart
