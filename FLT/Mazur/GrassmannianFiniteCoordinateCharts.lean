/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientSecondChart

/-!
# Finitely indexed original charts over local coefficient algebras

Fix one ambient basis. Selecting d distinct basis columns gives finitely many
original-base charts. Every quotient chart point over a local coefficient ring
belongs to one of these charts, retaining its full original relation.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M ι κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}

/-- A selected column set determines a chart with the prescribed complementary rank. -/
def finiteCoordinateChart (b : Module.Basis ι R M)
    (hκ : Fintype.card κ = Fintype.card ι - d) (a : Fin d ↪ ι) :
    AmbientChartIndex R M κ d :=
  selectedAmbientChartWithComplement b a
    (Fintype.equivOfCardEq ((selectedComplement_card a).trans hκ.symm))

variable {A : Type u} [CommRing A] [Algebra R A] [IsLocalRing A]

/-- An actual quotient chart over a local coefficient ring has the stated finite rank. -/
theorem ambientChartPoint_finrank (i : AmbientChartIndex R M κ d)
    (N : AmbientChartPoint (ambientChartBaseChange A i)) :
    Module.finrank A ((A ⊗[R] M) ⧸ N.val.toSubmodule) = d := by
  let e := LinearEquiv.ofBijective
    (N.val.toSubmodule.mkQ.comp (ambientChartSelected (ambientChartBaseChange A i))) N.property
  rw [← e.finrank_eq]
  exact Module.finrank_fin_fun A

/-- Finitely many original-base coordinate charts cover every local quotient chart point. -/
theorem exists_finiteCoordinateChart_local (b : Module.Basis ι R M)
    (hκ : Fintype.card κ = Fintype.card ι - d) (i : AmbientChartIndex R M κ d)
    (N : AmbientChartPoint (ambientChartBaseChange A i)) :
    ∃ a : Fin d ↪ ι, Function.Bijective
      (N.val.toSubmodule.mkQ.comp
        (ambientChartSelected (ambientChartBaseChange A (finiteCoordinateChart b hκ a)))) := by
  obtain ⟨a, c, hc⟩ := exists_selected_quotient_basis (Algebra.TensorProduct.basis A b)
    N.val.toSubmodule.mkQ (Submodule.mkQ_surjective _) (ambientChartPoint_finrank i N)
  refine ⟨a, ?_⟩
  rw [finiteCoordinateChart, selectedAmbientChart_baseChange_quotient]
  apply selectedColumnMap_bijective_of_basis _ c
  simpa only [Algebra.TensorProduct.basis_apply] using hc

end FLT.Mazur.GrassmannianChart
