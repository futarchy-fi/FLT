/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientBlocks

/-!
# Indexing all finite ambient decompositions

For fixed selected and complementary ranks, every split ambient basis is an index.
The coordinate change between two indices is constructed through the original
ambient module. Its selected summand is the actual summand of the second basis.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
  (ι : Type*) (d : ℕ)

/-- All ambient decompositions with the specified finite complementary index. -/
abbrev AmbientChartIndex := ((Fin d → R) × (ι → R)) ≃ₗ[R] M

variable {R M ι d}

/-- Every basis indexed by the selected and complementary coordinates gives a chart. -/
def ambientChartOfBasis [Fintype ι] (b : Module.Basis (Fin d ⊕ ι) R M) :
    AmbientChartIndex R M ι d :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin d) ι R R).symm.trans b.equivFun.symm

/-- The selected ambient summand belonging to a chart index. -/
def ambientChartSelected (i : AmbientChartIndex R M ι d) : (Fin d → R) →ₗ[R] M :=
  i.toLinearMap.comp (LinearMap.inl R _ _)

/-- The complementary ambient summand belonging to a chart index. -/
def ambientChartComplement (i : AmbientChartIndex R M ι d) : (ι → R) →ₗ[R] M :=
  i.toLinearMap.comp (LinearMap.inr R _ _)

/-- Coordinate change from the second ambient decomposition to the first. -/
def ambientChartChange (i j : AmbientChartIndex R M ι d) :
    ((Fin d → R) × (ι → R)) ≃ₗ[R] ((Fin d → R) × (ι → R)) := j.trans i.symm

/-- Self coordinate changes are identities. -/
@[simp] theorem ambientChartChange_self (i : AmbientChartIndex R M ι d) :
    ambientChartChange i i = LinearEquiv.refl R _ := by
  apply LinearEquiv.ext
  intro x
  exact i.symm_apply_apply x

/-- Reversing indices reverses the ambient coordinate change. -/
@[simp] theorem ambientChartChange_symm (i j : AmbientChartIndex R M ι d) :
    (ambientChartChange i j).symm = ambientChartChange j i := rfl

/-- Successive coordinate changes compose through the original ambient module. -/
@[simp] theorem ambientChartChange_trans (i j k : AmbientChartIndex R M ι d) :
    (ambientChartChange j k).trans (ambientChartChange i j) = ambientChartChange i k := by
  apply LinearEquiv.ext
  intro x
  exact congrArg i.symm (j.apply_symm_apply (k x))

/-- The coordinate change identifies the actual selected ambient summands. -/
theorem ambientChartChange_selected (i j : AmbientChartIndex R M ι d) :
    i.toLinearMap.comp ((ambientChartChange i j).toLinearMap.comp (LinearMap.inl R _ _)) =
      ambientChartSelected j := by
  apply LinearMap.ext
  intro x
  exact i.apply_symm_apply (j (x, 0))

/-- The four blocks select precisely the second ambient summand in first-chart coordinates. -/
theorem ambientChartChange_selected_blocks [Finite ι] (i j : AmbientChartIndex R M ι d) :
    i.toLinearMap.comp (matrixSelectedSummand
      (ambientBlockP (ambientChartChange i j).toLinearMap)
      (ambientBlockQ (ambientChartChange i j).toLinearMap)) = ambientChartSelected j := by
  classical
  let _ := Fintype.ofFinite ι
  rw [← ambientChartChange_selected i j]
  congr 1
  simp only [matrixSelectedSummand, ambientBlockP, ambientBlockQ, Matrix.toLin'_toMatrix']
  rfl

end FLT.Mazur.GrassmannianChart
