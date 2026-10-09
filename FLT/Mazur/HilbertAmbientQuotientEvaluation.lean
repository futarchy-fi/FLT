/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertAmbientChartClassification

/-!
# Actual quotient algebras inside an affine ambient scheme

A point of the closed ambient chart supplies a surjective evaluation from
the actual ambient quotient ring over the test base to its free quotient
algebra. Its kernel pulls back to the full original polynomial ideal.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.HilbertChart

universe u v

variable (R : Type u) [CommRing R] (I : Type v) (d : ℕ)
variable (w : Fin d → MvPolynomial I R) (K : Ideal (MvPolynomial I R))

/-- Cache the coefficient ring for ambient quotient evaluation. -/
local instance ambientEvaluationCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache the chart ring for ambient quotient evaluation. -/
local instance ambientEvaluationChartRing : CommRing (ChartRing R I d w) := inferInstance

variable (S : Type*) [CommRing S] [Algebra R S]
variable (g : AmbientChartRing R I d w K →ₐ[R] S)

/-- Evaluate the actual affine ambient quotient in the family of a closed-chart point. -/
def ambientPointEvaluation :
    (MvPolynomial I S ⧸ K.map (MvPolynomial.map (algebraMap R S))) →ₐ[S]
      PointFiber R I d w (ambientChartForget R I d w K S g) :=
  Ideal.Quotient.liftₐ _ (pointEvaluation R I d w (ambientChartForget R I d w K S g))
    (ambientChartForget_contains R I d w K S g)

/-- Ambient quotient evaluation recovers the original polynomial evaluation. -/
theorem ambientPointEvaluation_mk (p : MvPolynomial I S) :
    ambientPointEvaluation R I d w K S g
        (Ideal.Quotient.mk (K.map (MvPolynomial.map (algebraMap R S))) p) =
      pointEvaluation R I d w (ambientChartForget R I d w K S g) p := rfl

/-- Every vector in the free family algebra comes from the actual ambient quotient. -/
theorem ambientPointEvaluation_surjective :
    Function.Surjective (ambientPointEvaluation R I d w K S g) := by
  intro x
  obtain ⟨p, hp⟩ := pointEvaluation_surjective R I d w (ambientChartForget R I d w K S g) x
  exact ⟨Ideal.Quotient.mk _ p, hp⟩

/-- The actual ideal of the closed family inside the ambient quotient ring. -/
def ambientPointIdeal : Ideal (MvPolynomial I S ⧸ K.map (MvPolynomial.map (algebraMap R S))) :=
  RingHom.ker (ambientPointEvaluation R I d w K S g).toRingHom

/-- The quotient-ambient ideal pulls back to the full original polynomial ideal. -/
theorem ambientPointIdeal_comap :
    (ambientPointIdeal R I d w K S g).comap
        (Ideal.Quotient.mk (K.map (MvPolynomial.map (algebraMap R S)))) =
      pointIdeal R I d w (ambientChartForget R I d w K S g) := by
  ext p
  rfl

/-- The actual ambient closed quotient is the original free point-family algebra. -/
def ambientPointQuotientEquiv :
    ((MvPolynomial I S ⧸ K.map (MvPolynomial.map (algebraMap R S))) ⧸
        ambientPointIdeal R I d w K S g) ≃ₐ[S]
      PointFiber R I d w (ambientChartForget R I d w K S g) :=
  Ideal.quotientKerAlgEquivOfSurjective (ambientPointEvaluation_surjective R I d w K S g)

/-- The quotient comparison retains the actual polynomial evaluation map. -/
theorem ambientPointQuotientEquiv_mk (p : MvPolynomial I S) :
    ambientPointQuotientEquiv R I d w K S g
        (Ideal.Quotient.mk (ambientPointIdeal R I d w K S g)
          (Ideal.Quotient.mk (K.map (MvPolynomial.map (algebraMap R S))) p)) =
      pointEvaluation R I d w (ambientChartForget R I d w K S g) p := rfl

end FLT.Mazur.HilbertChart
