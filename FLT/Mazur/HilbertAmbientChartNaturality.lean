/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertAmbientChartClassification
public import FLT.Mazur.HilbertChartClassificationNaturality

/-!
# Naturality of closed ambient chart classification

Scalar extension preserves full containment of the original ambient ideal.
The actual closed-chart equivalence and its inverse commute with extension
of quotient ideals, giving the compatibility needed for ambient chart gluing.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.HilbertChart

universe u v

variable (R : Type u) [CommRing R] (I : Type v) (d : ℕ)
variable (w : Fin d → MvPolynomial I R) (K : Ideal (MvPolynomial I R))

/-- Cache the coefficient ring for scalar extension of closed charts. -/
local instance ambientNaturalCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache the chart ring for scalar extension of closed charts. -/
local instance ambientNaturalChartRing : CommRing (ChartRing R I d w) := inferInstance

variable (S T : Type*) [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- Scalar extension of an actual ambient ideal preserves its prescribed basis and containment. -/
def baseChangeAmbientIdeal (J : AmbientPrescribedBasisIdeals R I d w K S) :
    AmbientPrescribedBasisIdeals R I d w K T := by
  refine ⟨baseChangeIdeal R I d w S T J.val, ?_⟩
  have h : (K.map (MvPolynomial.map (algebraMap R S))).map
      (MvPolynomial.map (algebraMap S T)) ≤ J.val.val.map
        (MvPolynomial.map (algebraMap S T)) := Ideal.map_mono J.property
  rw [Ideal.map_map] at h
  have hm : (MvPolynomial.map (σ := I) (algebraMap S T)).comp
      (MvPolynomial.map (algebraMap R S)) =
      MvPolynomial.map (algebraMap R T) := by
    ext x <;> simp [IsScalarTower.algebraMap_apply R S T]
  rw [hm] at h
  exact h

/-- The actual closed-chart equivalence carries parameter composition to full ideal extension. -/
theorem ambientChartClassification_natural (g : AmbientChartRing R I d w K →ₐ[R] S) :
    ambientChartClassification R I d w K T ((IsScalarTower.toAlgHom R S T).comp g) =
      baseChangeAmbientIdeal R I d w K S T (ambientChartClassification R I d w K S g) := by
  apply Subtype.ext
  exact chartClassification_natural R I d w S T (ambientChartForget R I d w K S g)

/-- Classifying the extended ambient quotient is composition of its original closed-chart map. -/
theorem ambientChartClassification_symm_natural
    (J : AmbientPrescribedBasisIdeals R I d w K S) :
    (ambientChartClassification R I d w K T).symm (baseChangeAmbientIdeal R I d w K S T J) =
      (IsScalarTower.toAlgHom R S T).comp ((ambientChartClassification R I d w K S).symm J) := by
  apply (ambientChartClassification R I d w K T).injective
  rw [Equiv.apply_symm_apply, ambientChartClassification_natural, Equiv.apply_symm_apply]

end FLT.Mazur.HilbertChart
