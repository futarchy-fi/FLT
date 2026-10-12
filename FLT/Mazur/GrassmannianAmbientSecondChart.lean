/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientPointTransition
public import FLT.Mazur.GrassmannianAmbientChartRepresentation

/-!
# The second ambient chart is exactly a determinant open

Transport through the actual quotient equivalence compares second-basis membership
in original ambient coordinates with the split determinant criterion, over every algebra.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype κ] {d : ℕ}

omit [Fintype κ] in
/-- Transport preserves membership in the second original ambient chart. -/
theorem ambientChartPointOfSplit_second_iff [Finite κ] (i j : AmbientChartIndex R M κ d)
    (N : SplitChart R (κ → R) d) :
    Function.Bijective ((ambientChartPointOfSplit i N).val.toSubmodule.mkQ.comp
      (ambientChartSelected j)) ↔
      Function.Bijective (N.val.toSubmodule.mkQ.comp (matrixSelectedSummand
        (ambientBlockP (ambientChartChange i j).toLinearMap)
        (ambientBlockQ (ambientChartChange i j).toLinearMap))) := by
  let _ := Fintype.ofFinite κ
  let e := ambientTransportQuotientEquiv i N.val
  have he : e.toLinearMap.comp
      ((ambientChartPointOfSplit i N).val.toSubmodule.mkQ.comp (ambientChartSelected j)) =
      N.val.toSubmodule.mkQ.comp (matrixSelectedSummand
        (ambientBlockP (ambientChartChange i j).toLinearMap)
        (ambientBlockQ (ambientChartChange i j).toLinearMap)) := by
    apply LinearMap.ext
    intro x
    change ambientTransportQuotientEquiv i N.val
      (Submodule.Quotient.mk (ambientChartSelected j x)) = _
    rw [ambientTransportQuotientEquiv, LinearMap.quotKerEquivOfSurjective_apply_mk]
    have hj := congrArg (fun f : (Fin d → R) →ₗ[R] M ↦ f x)
      (ambientChartChange_selected_blocks i j)
    change N.val.toSubmodule.mkQ (i.symm (ambientChartSelected j x)) = _
    rw [← hj]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [← he]
  exact (e.bijective.of_comp_iff' _).symm

variable {A : Type u} [CommRing A] [Algebra R A]

/-- Scalar extension retains the exact second-chart condition in the original base blocks. -/
theorem ambientChartPointOfSplit_baseChange_second_iff (i j : AmbientChartIndex R M κ d)
    (N : SplitChart A (κ → A) d) :
    Function.Bijective
      ((ambientChartPointOfSplit (ambientChartBaseChange A i) N).val.toSubmodule.mkQ.comp
       (ambientChartSelected (ambientChartBaseChange A j))) ↔
      Function.Bijective (N.val.toSubmodule.mkQ.comp (matrixSelectedSummand
        ((ambientBlockP (ambientChartChange i j).toLinearMap).map (algebraMap R A))
        ((ambientBlockQ (ambientChartChange i j).toLinearMap).map (algebraMap R A)))) := by
  rw [ambientChartPointOfSplit_second_iff, ambientChartChange_baseChange,
    ambientBlockP_baseChange, ambientBlockQ_baseChange]

/-- The defining determinant is a unit precisely for original double-chart membership. -/
theorem ambientChartPolynomial_second_iff (i j : AmbientChartIndex R M κ d)
    (f : MvPolynomial (Fin d × κ) R →ₐ[R] A) :
    Function.Bijective ((ambientChartPointOfSplit (ambientChartBaseChange A i)
      (splitChartPolynomialEquiv R A κ d f)).val.toSubmodule.mkQ.comp
        (ambientChartSelected (ambientChartBaseChange A j))) ↔
      IsUnit (f (overlapPolynomial (ambientBlockP (ambientChartChange i j).toLinearMap)
        (ambientBlockQ (ambientChartChange i j).toLinearMap))) := by
  rw [ambientChartPointOfSplit_baseChange_second_iff, overlapPolynomial_isUnit_iff]

end FLT.Mazur.GrassmannianChart
