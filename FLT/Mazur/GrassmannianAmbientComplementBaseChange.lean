/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientIndexBaseChange

/-!
# Complementary ambient vectors and scalar extension

The complementary columns in an original-base chart are the unselected original
basis vectors. This identification is preserved by every coefficient extension.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M ι κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}

/-- Inserting a complementary standard vector recovers its original ambient basis vector. -/
theorem ambientChartOfBasis_complement_basis
    (b : Module.Basis (Fin d ⊕ κ) R M) (j : κ) :
    ambientChartComplement (ambientChartOfBasis b) (Pi.basisFun R κ j) =
      b (Sum.inr j) := by
  classical
  apply b.equivFun.injective
  change b.equivFun (b.equivFun.symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  ext k
  cases k <;> simp [Module.Basis.equivFun_self, Pi.basisFun_apply, Pi.single_apply, eq_comm]

omit [Fintype ι] in
/-- Complement reindexing retains precisely the unselected original basis vectors. -/
theorem selectedAmbientChartWithComplement_complement_basis
    (b : Module.Basis ι R M) (a : Fin d ↪ ι) (e : SelectedComplement a ≃ κ) (j : κ) :
    ambientChartComplement (selectedAmbientChartWithComplement b a e)
      (Pi.basisFun R κ j) = b (e.symm j).val := by
  change ambientChartComplement (ambientChartOfBasis _) _ = _
  rw [ambientChartOfBasis_complement_basis]
  simp only [Module.Basis.reindex_apply, Equiv.sumCongr_symm, Equiv.refl_symm,
    Equiv.sumCongr_apply, Sum.map_inr, selectedAmbientBasis, Equiv.symm_symm]
  rfl

variable (A : Type u) [CommRing A] [Algebra R A]

omit [Fintype ι] in
/-- Split scalar extension preserves each complementary standard vector. -/
theorem splitAmbientTensorEquiv_complement_basis (j : κ) :
    splitAmbientTensorEquiv A κ d
      (1 ⊗ₜ[R] ((0 : Fin d → R), Pi.basisFun R κ j)) =
      (0, Pi.basisFun A κ j) := by
  classical
  rw [splitAmbientTensorEquiv_tmul]
  ext k <;> simp [Pi.basisFun_apply, Pi.single_apply]

omit [Fintype ι] in
/-- The complementary ambient summand commutes with coefficient extension. -/
theorem ambientChartBaseChange_complement_basis (i : AmbientChartIndex R M κ d) (j : κ) :
    ambientChartComplement (ambientChartBaseChange A i) (Pi.basisFun A κ j) =
      1 ⊗ₜ[R] ambientChartComplement i (Pi.basisFun R κ j) := by
  change (i.baseChange R A) ((splitAmbientTensorEquiv A κ d).symm
    (0, Pi.basisFun A κ j)) = _
  rw [← splitAmbientTensorEquiv_complement_basis (R := R) (d := d) A,
    LinearEquiv.symm_apply_apply, LinearEquiv.baseChange_tmul]
  rfl

omit [Fintype ι] in
/-- Original unselected columns remain the same pure tensors over every coefficient ring. -/
theorem selectedAmbientChart_baseChange_complement_basis (b : Module.Basis ι R M)
    (a : Fin d ↪ ι) (e : SelectedComplement a ≃ κ) (j : κ) :
    ambientChartComplement
        (ambientChartBaseChange A (selectedAmbientChartWithComplement b a e))
        (Pi.basisFun A κ j) = 1 ⊗ₜ[R] b (e.symm j).val := by
  rw [ambientChartBaseChange_complement_basis,
    selectedAmbientChartWithComplement_complement_basis]

end FLT.Mazur.GrassmannianChart
