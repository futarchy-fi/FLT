/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientChartIndex
public import FLT.Mazur.GrassmannianSelectedColumnsLocalization
public import Mathlib.Data.Fintype.Card

/-!
# Ambient chart indices from selected basis columns

An injection selecting d ambient basis vectors extends to a decomposition by the
remaining vectors. The complementary rank is the ambient rank minus d, and the
selected summand is exactly the original column map.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M ι : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] {d : ℕ}

/-- The original ambient basis vectors not selected by the quotient basis. -/
abbrev SelectedComplement (a : Fin d ↪ ι) := {i : ι // i ∉ Set.range a}

instance (a : Fin d ↪ ι) : Fintype (SelectedComplement a) := by
  classical
  exact Subtype.fintype _

/-- Selected and unselected ambient indices form the entire original basis index. -/
def selectedAmbientSumEquiv (a : Fin d ↪ ι) : (Fin d ⊕ SelectedComplement a) ≃ ι := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective a a.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range a))

omit [Fintype ι] in
/-- The selected part of the reindexing is the specified injection. -/
@[simp] theorem selectedAmbientSumEquiv_inl (a : Fin d ↪ ι) (i : Fin d) :
    selectedAmbientSumEquiv a (Sum.inl i) = a i := rfl

/-- The complement has the required ambient rank minus selected rank. -/
theorem selectedComplement_card (a : Fin d ↪ ι) :
    Fintype.card (SelectedComplement a) = Fintype.card ι - d := by
  classical
  change Fintype.card {i : ι // i ∉ Set.range a} = _
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_range, Fintype.card_fin]

/-- Reindex the original ambient basis without changing any of its vectors. -/
def selectedAmbientBasis (b : Module.Basis ι R M) (a : Fin d ↪ ι) :
    Module.Basis (Fin d ⊕ SelectedComplement a) R M :=
  b.reindex (selectedAmbientSumEquiv a).symm

/-- The actual ambient decomposition defined by the selected basis columns. -/
def selectedAmbientChart (b : Module.Basis ι R M) (a : Fin d ↪ ι) :
    AmbientChartIndex R M (SelectedComplement a) d :=
  ambientChartOfBasis (selectedAmbientBasis b a)

/-- Inserting a standard selected basis vector returns the corresponding ambient vector. -/
theorem ambientChartOfBasis_selected_basis {κ : Type*} [Fintype κ]
    (b : Module.Basis (Fin d ⊕ κ) R M) (i : Fin d) :
    ambientChartSelected (ambientChartOfBasis b) (Pi.basisFun R (Fin d) i) =
      b (Sum.inl i) := by
  classical
  apply b.equivFun.injective
  change b.equivFun (b.equivFun.symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  ext j
  cases j <;> simp [Module.Basis.equivFun_self, Pi.basisFun_apply, Pi.single_apply, eq_comm]

/-- The selected summand is the column map of the original selected ambient vectors. -/
theorem selectedAmbientChart_selected (b : Module.Basis ι R M) (a : Fin d ↪ ι) :
    ambientChartSelected (selectedAmbientChart b a) =
      selectedColumnMap (fun i ↦ b (a i)) := by
  apply (Pi.basisFun R (Fin d)).ext
  intro i
  rw [selectedColumnMap, Module.Basis.constr_basis]
  change ambientChartSelected (ambientChartOfBasis (selectedAmbientBasis b a)) _ = _
  rw [ambientChartOfBasis_selected_basis]
  simp only [selectedAmbientBasis, Module.Basis.reindex_apply, Equiv.symm_symm,
    selectedAmbientSumEquiv_inl]

/-- Reindex the complementary columns by any chosen index set of the correct size. -/
def selectedAmbientChartWithComplement {κ : Type*} [Fintype κ]
    (b : Module.Basis ι R M) (a : Fin d ↪ ι) (e : SelectedComplement a ≃ κ) :
    AmbientChartIndex R M κ d :=
  ambientChartOfBasis ((selectedAmbientBasis b a).reindex
    (Equiv.sumCongr (Equiv.refl (Fin d)) e))

omit [Fintype ι] in
/-- Changing only the complementary indices preserves the selected column map. -/
theorem selectedAmbientChartWithComplement_selected {κ : Type*} [Fintype κ]
    (b : Module.Basis ι R M) (a : Fin d ↪ ι) (e : SelectedComplement a ≃ κ) :
    ambientChartSelected (selectedAmbientChartWithComplement b a e) =
      selectedColumnMap (fun i ↦ b (a i)) := by
  apply (Pi.basisFun R (Fin d)).ext
  intro i
  rw [selectedColumnMap, Module.Basis.constr_basis]
  change ambientChartSelected (ambientChartOfBasis _) _ = _
  rw [ambientChartOfBasis_selected_basis]
  simp only [Module.Basis.reindex_apply, Equiv.sumCongr_symm, Equiv.refl_symm,
    Equiv.sumCongr_apply, Equiv.refl_apply, Sum.map_inl, selectedAmbientBasis,
    Equiv.symm_symm, selectedAmbientSumEquiv_inl]

end FLT.Mazur.GrassmannianChart
