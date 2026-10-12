/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianSelectedAmbientIndex

/-!
# Principal chart coverage for original ambient quotients

Every finite projective rank-d quotient of a finite free ambient module belongs
locally to an actual ambient chart. The complementary rank is fixed in advance.
The principal coefficient neighborhoods cover the entire coefficient spectrum.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M Q ι κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Q] [Module R Q] [Fintype ι] [Fintype κ] {d : ℕ}

omit [Fintype ι] in
/-- The quotient of the reindexed selected summand is precisely the original column map. -/
theorem selectedAmbientChart_quotient (b : Module.Basis ι R M) (a : Fin d ↪ ι)
    (e : SelectedComplement a ≃ κ) (q : M →ₗ[R] Q) :
    q.comp (ambientChartSelected (selectedAmbientChartWithComplement b a e)) =
      selectedColumnMap (fun i ↦ q (b (a i))) := by
  rw [selectedAmbientChartWithComplement_selected]
  apply (Pi.basisFun R (Fin d)).ext
  intro i
  simp only [LinearMap.comp_apply, selectedColumnMap, Module.Basis.constr_basis]

/-- Actual ambient charts cover a finite projective quotient near every coefficient prime. -/
theorem exists_ambient_quotient_chart_away [Module.Finite R Q] [Module.Projective R Q]
    (b : Module.Basis ι R M) (q : M →ₗ[R] Q) (hq : Function.Surjective q)
    (hκ : Fintype.card κ = Fintype.card ι - d)
    (p : PrimeSpectrum R) (hd : Module.rankAtStalk Q p = d) :
    ∃ (i : AmbientChartIndex R M κ d) (r : R), r ∉ p.asIdeal ∧
      Function.Bijective (LocalizedModule.map (.powers r)
        (q.comp (ambientChartSelected i))) := by
  obtain ⟨a, r, hr, hb⟩ := exists_selected_columns_away b q hq p hd
  let e : SelectedComplement a ≃ κ :=
    Fintype.equivOfCardEq ((selectedComplement_card a).trans hκ.symm)
  refine ⟨selectedAmbientChartWithComplement b a e, r, hr, ?_⟩
  rw [selectedAmbientChart_quotient]
  exact hb

/-- Principal coefficients on which some fixed-rank ambient summand trivializes the quotient. -/
def ambientQuotientTrivializers (q : M →ₗ[R] Q) (κ : Type u) (d : ℕ) : Set R :=
  {r | ∃ i : AmbientChartIndex R M κ d,
    Function.Bijective (LocalizedModule.map (.powers r) (q.comp (ambientChartSelected i)))}

/-- The chart-trivializing coefficients generate the unit ideal. -/
theorem span_ambientQuotientTrivializers [Module.Finite R Q] [Module.Projective R Q]
    (b : Module.Basis ι R M) (q : M →ₗ[R] Q) (hq : Function.Surjective q)
    (hκ : Fintype.card κ = Fintype.card ι - d)
    (hd : ∀ p, Module.rankAtStalk (R := R) Q p = d) :
    Ideal.span (ambientQuotientTrivializers q κ d) = ⊤ := by
  by_contra h
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ h
  let _ := hp.isPrime
  obtain ⟨i, r, hr, hi⟩ := exists_ambient_quotient_chart_away b q hq hκ ⟨p, inferInstance⟩
    (hd ⟨p, inferInstance⟩)
  exact hr (hle (Ideal.subset_span ⟨i, hi⟩))

/-- The constructed principal coefficient neighborhoods cover the whole spectrum. -/
theorem ambientQuotientTrivializers_cover [Module.Finite R Q] [Module.Projective R Q]
    (b : Module.Basis ι R M) (q : M →ₗ[R] Q) (hq : Function.Surjective q)
    (hκ : Fintype.card κ = Fintype.card ι - d)
    (hd : ∀ p, Module.rankAtStalk (R := R) Q p = d) :
    ⨆ r : ambientQuotientTrivializers q κ d, PrimeSpectrum.basicOpen r.val = ⊤ := by
  rw [PrimeSpectrum.iSup_basicOpen_eq_top_iff]
  simpa only [Subtype.range_coe] using span_ambientQuotientTrivializers b q hq hκ hd

/-- Coverage applies to the full original relation of every quotient Grassmannian point. -/
theorem grassmannian_ambient_chart_cover (b : Module.Basis ι R M)
    (N : Module.Grassmannian R M d) (hκ : Fintype.card κ = Fintype.card ι - d) :
    ⨆ r : ambientQuotientTrivializers N.toSubmodule.mkQ κ d,
      PrimeSpectrum.basicOpen r.val = ⊤ :=
  ambientQuotientTrivializers_cover b N.toSubmodule.mkQ (Submodule.mkQ_surjective _)
    hκ N.rankAtStalk_eq

end FLT.Mazur.GrassmannianChart
