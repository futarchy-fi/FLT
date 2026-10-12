/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientIndexBaseChange

/-!
# Original-base ambient charts cover quotient points over every coefficient algebra

For an A-valued Grassmannian point, the selected ambient chart is defined over R.
Only its coefficient principal neighborhood is chosen over A. Thus the coverage
uses the same chart indices as the glued R-scheme, not a larger A-indexed atlas.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M ι κ : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Fintype ι] [Fintype κ] {d : ℕ}

omit [Fintype ι] in
/-- The original-base selected summand evaluates to the same quotient columns over A. -/
theorem selectedAmbientChart_baseChange_quotient (b : Module.Basis ι R M)
    (a : Fin d ↪ ι) (e : SelectedComplement a ≃ κ)
    (N : Module.Grassmannian A (A ⊗[R] M) d) :
    N.toSubmodule.mkQ.comp
      (ambientChartSelected (ambientChartBaseChange A
        (selectedAmbientChartWithComplement b a e))) =
      selectedColumnMap (fun j ↦ N.toSubmodule.mkQ (1 ⊗ₜ[R] b (a j))) := by
  apply (Pi.basisFun A (Fin d)).ext
  intro j
  rw [LinearMap.comp_apply, selectedAmbientChart_baseChange_basis]
  simp only [selectedColumnMap, Module.Basis.constr_basis]

/-- Every coefficient prime lies in an original-base chart on a principal neighborhood. -/
theorem exists_original_base_chart_away (b : Module.Basis ι R M)
    (N : Module.Grassmannian A (A ⊗[R] M) d)
    (hκ : Fintype.card κ = Fintype.card ι - d) (p : PrimeSpectrum A) :
    ∃ (i : AmbientChartIndex R M κ d) (r : A), r ∉ p.asIdeal ∧
      Function.Bijective (LocalizedModule.map (.powers r)
        (N.toSubmodule.mkQ.comp (ambientChartSelected (ambientChartBaseChange A i)))) := by
  obtain ⟨a, r, hr, hb⟩ := exists_selected_columns_away
    (Algebra.TensorProduct.basis A b) N.toSubmodule.mkQ
    (Submodule.mkQ_surjective _) p (N.rankAtStalk_eq p)
  let e : SelectedComplement a ≃ κ :=
    Fintype.equivOfCardEq ((selectedComplement_card a).trans hκ.symm)
  refine ⟨selectedAmbientChartWithComplement b a e, r, hr, ?_⟩
  rw [selectedAmbientChart_baseChange_quotient]
  simpa only [Algebra.TensorProduct.basis_apply] using hb

/-- Coefficients on which the point lies in the scalar extension of an original-base chart. -/
def originalBaseChartTrivializers (N : Module.Grassmannian A (A ⊗[R] M) d)
    (κ : Type u) [Fintype κ] : Set A :=
  {r | ∃ i : AmbientChartIndex R M κ d,
    Function.Bijective (LocalizedModule.map (.powers r)
      (N.toSubmodule.mkQ.comp (ambientChartSelected (ambientChartBaseChange A i))))}

/-- The original-base chart neighborhoods generate the unit ideal in every coefficient algebra. -/
theorem span_originalBaseChartTrivializers (b : Module.Basis ι R M)
    (N : Module.Grassmannian A (A ⊗[R] M) d)
    (hκ : Fintype.card κ = Fintype.card ι - d) :
    Ideal.span (originalBaseChartTrivializers N κ) = ⊤ := by
  by_contra h
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ h
  let _ := hp.isPrime
  obtain ⟨i, r, hr, hi⟩ := exists_original_base_chart_away b N hκ ⟨p, inferInstance⟩
  exact hr (hle (Ideal.subset_span ⟨i, hi⟩))

/-- Original-base charts locally cover every point of the actual Grassmannian functor. -/
theorem originalBaseChartTrivializers_cover (b : Module.Basis ι R M)
    (N : Module.Grassmannian A (A ⊗[R] M) d)
    (hκ : Fintype.card κ = Fintype.card ι - d) :
    ⨆ r : originalBaseChartTrivializers N κ, PrimeSpectrum.basicOpen r.val = ⊤ := by
  rw [PrimeSpectrum.iSup_basicOpen_eq_top_iff]
  simpa only [Subtype.range_coe] using span_originalBaseChartTrivializers b N hκ

end FLT.Mazur.GrassmannianChart
