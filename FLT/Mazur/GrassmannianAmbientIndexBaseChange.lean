/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianSelectedAmbientIndex

/-!
# Scalar extension of actual ambient chart indices

The ambient decomposition is chosen over the original base ring. After scalar
extension its selected basis vectors are the tensors of those same original
vectors, so coefficient-local coverage uses the original chart family.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M ι κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}
variable (A : Type u) [CommRing A] [Algebra R A]

/-- Scalar extension of an ambient decomposition through finite split coordinates. -/
def ambientChartBaseChange (i : AmbientChartIndex R M κ d) :
    AmbientChartIndex A (A ⊗[R] M) κ d :=
  (splitAmbientTensorEquiv A κ d).symm.trans (i.baseChange R A)

omit [Fintype ι] in
/-- Split scalar extension sends the selected standard vector to the selected standard vector. -/
theorem splitAmbientTensorEquiv_selected_basis (j : Fin d) :
    splitAmbientTensorEquiv A κ d
      (1 ⊗ₜ[R] ((Pi.basisFun R (Fin d) j), (0 : κ → R))) =
      (Pi.basisFun A (Fin d) j, 0) := by
  classical
  rw [splitAmbientTensorEquiv_tmul]
  ext k <;> simp [Pi.basisFun_apply, Pi.single_apply]

omit [Fintype ι] in
/-- The selected ambient vectors commute with scalar extension. -/
theorem ambientChartBaseChange_selected_basis (i : AmbientChartIndex R M κ d)
    (j : Fin d) :
    ambientChartSelected (ambientChartBaseChange A i) (Pi.basisFun A (Fin d) j) =
      1 ⊗ₜ[R] ambientChartSelected i (Pi.basisFun R (Fin d) j) := by
  change (i.baseChange R A) ((splitAmbientTensorEquiv A κ d).symm
    (Pi.basisFun A (Fin d) j, 0)) = _
  rw [← splitAmbientTensorEquiv_selected_basis (R := R) (κ := κ) A, LinearEquiv.symm_apply_apply,
    LinearEquiv.baseChange_tmul]
  rfl

omit [Fintype ι] in
/-- Original selected ambient columns remain the same columns after scalar extension. -/
theorem selectedAmbientChart_baseChange_basis (b : Module.Basis ι R M)
    (a : Fin d ↪ ι) (e : SelectedComplement a ≃ κ) (j : Fin d) :
    ambientChartSelected
      (ambientChartBaseChange A (selectedAmbientChartWithComplement b a e))
      (Pi.basisFun A (Fin d) j) = 1 ⊗ₜ[R] b (a j) := by
  rw [ambientChartBaseChange_selected_basis, selectedAmbientChartWithComplement_selected]
  simp only [selectedColumnMap, Module.Basis.constr_basis]

omit [Fintype ι] in
/-- The selected map in an original-base chart is the tensor-extended column map. -/
theorem selectedAmbientChart_baseChange_selected (b : Module.Basis ι R M)
    (a : Fin d ↪ ι) (e : SelectedComplement a ≃ κ) :
    ambientChartSelected
      (ambientChartBaseChange A (selectedAmbientChartWithComplement b a e)) =
      selectedColumnMap (fun j ↦ (1 : A) ⊗ₜ[R] b (a j)) := by
  apply (Pi.basisFun A (Fin d)).ext
  intro j
  rw [selectedAmbientChart_baseChange_basis]
  simp only [selectedColumnMap, Module.Basis.constr_basis]

end FLT.Mazur.GrassmannianChart
