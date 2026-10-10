/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartClassification
public import FLT.Mazur.HilbertChartBaseChange
public import FLT.Mazur.HilbertPolynomialQuotientBaseChange

/-!
# Naturality for actual prescribed-basis quotient ideals

The chart equivalence commutes with extension of the actual ambient ideal.
The basis after base change comes from the tensor quotient comparison.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.HilbertChart

universe u v

variable (R : Type u) [CommRing R] (I : Type v) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)
variable (S T : Type*) [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
variable [Algebra R T] [IsScalarTower R S T]

/-- Extend the actual ambient ideal; its prescribed basis is transported from the tensor product. -/
def baseChangeIdeal (J : PrescribedBasisIdeals R I d w S) : PrescribedBasisIdeals R I d w T := by
  refine ⟨J.val.map (MvPolynomial.map (algebraMap S T)),
    ((quotientBasis R I d w S J).baseChange T).map
      (polynomialQuotientBaseChangeEquiv I S T J.val).toLinearEquiv, ?_⟩
  intro i
  rw [Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply, Module.Basis.baseChange_apply,
    ← quotientBasis_spec R I d w S J i, quotientGenerator_evaluation,
    polynomialQuotientBaseChangeEquiv_tmul, one_smul, MvPolynomial.map_map,
    ← IsScalarTower.algebraMap_eq R S T]

/-- Classifying the extended ideal is composition of its original classifying map. -/
theorem idealClassifyingMap_baseChangeIdeal (J : PrescribedBasisIdeals R I d w S) :
    idealClassifyingMap R I d w T (baseChangeIdeal R I d w S T J) =
      (IsScalarTower.toAlgHom R S T).comp (idealClassifyingMap R I d w S J) := by
  let b := (quotientBasis R I d w S J).baseChange T
  let y := baseChangedGenerator (S := S) I (quotientGenerator I S J.val) T
  have hy := baseChangedGenerator_basis R I d (quotientBasis R I d w S J)
    (quotientGenerator I S J.val) T w (quotientBasis_spec R I d w S J)
  have he := classifyingMap_equiv R I d b
    (quotientBasis R I d w T (baseChangeIdeal R I d w S T J)) y
    (quotientGenerator I T (baseChangeIdeal R I d w S T J).val)
    (polynomialQuotientBaseChangeEquiv I S T J.val) w hy
    (quotientBasis_spec R I d w T (baseChangeIdeal R I d w S T J))
    (fun i ↦ polynomialQuotientBaseChangeEquiv_generator I S T J.val i)
  change classifyingMap R I d _ _ w _ = _
  rw [← he, classifyingMap_baseChange]
  rfl

/-- The classification equivalence carries composition of chart points to ideal extension. -/
theorem chartClassification_natural (f : ChartRing R I d w →ₐ[R] S) :
    chartClassification R I d w T ((IsScalarTower.toAlgHom R S T).comp f) =
      baseChangeIdeal R I d w S T (chartClassification R I d w S f) := by
  apply (chartClassification R I d w T).symm.injective
  change (chartClassification R I d w T).symm
    (chartClassification R I d w T ((IsScalarTower.toAlgHom R S T).comp f)) = _
  rw [Equiv.symm_apply_apply]
  change _ = idealClassifyingMap R I d w T
    (baseChangeIdeal R I d w S T (idealOfPoint R I d w f))
  rw [idealClassifyingMap_baseChangeIdeal, idealClassifyingMap_idealOfPoint]

end FLT.Mazur.HilbertChart
