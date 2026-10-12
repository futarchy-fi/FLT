/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientClassifyingInjective

/-!
# Affine factorization through an original Grassmannian chart

A classifying morphism factors through a specified chart exactly when the
selected columns are a basis of the full original quotient. Base compatibility
of a factorization follows from its composite; it is not an extra hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M κ : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}
  {ι : Type u} [Fintype ι] (b : Module.Basis ι R M)
  (hκ : Fintype.card κ = Fintype.card ι - d)
  (N : Module.Grassmannian A (A ⊗[R] M) d) (i : AmbientChartIndex R M κ d)

/-- An actual affine chart factorization detects precisely its selected quotient basis. -/
theorem ambientClassifyingMap_factors_chart_iff :
    (∃ g : Spec (.of A) ⟶ splitChartScheme R κ d,
      g ≫ ambientGrassmannianChart R M κ d i = ambientClassifyingMap b N hκ) ↔
      Function.Bijective
        (N.toSubmodule.mkQ.comp (ambientChartSelected (ambientChartBaseChange A i))) := by
  constructor
  · rintro ⟨g, hg⟩
    have hs : g ≫ splitChartStructure R κ d = Spec.algebraMap R A := by
      rw [← ambientGrassmannianChart_over R M κ d i, ← Category.assoc, hg,
        ambientClassifyingMap_over]
    let P := ambientChartSchemePointEquiv i ⟨g, hs⟩
    have he : ambientClassifyingMap b N hκ = ambientGluedChartPoint i P := by
      unfold ambientGluedChartPoint P
      rw [Equiv.symm_apply_apply]
      exact hg.symm
    have hn := (ambientClassifyingMap_eq_chart_iff b hκ N i P).mp he
    rw [hn]
    exact P.property
  · intro h
    let P : AmbientChartPoint (ambientChartBaseChange A i) := ⟨N, h⟩
    exact ⟨((ambientChartSchemePointEquiv i).symm P).val,
      (ambientClassifyingMap_ofChart b hκ i P).symm⟩

/-- The factorization, when it exists, is unique as a scheme morphism. -/
theorem ambientClassifyingMap_unique_chart_iff :
    (∃! g : Spec (.of A) ⟶ splitChartScheme R κ d,
      g ≫ ambientGrassmannianChart R M κ d i = ambientClassifyingMap b N hκ) ↔
      Function.Bijective
        (N.toSubmodule.mkQ.comp (ambientChartSelected (ambientChartBaseChange A i))) := by
  rw [← ambientClassifyingMap_factors_chart_iff b hκ N i]
  constructor
  · exact fun h ↦ h.exists
  · rintro ⟨g, hg⟩
    exact ⟨g, hg, fun k hk ↦ (cancel_mono
      (ambientGrassmannianChart R M κ d i)).mp (hk.trans hg.symm)⟩

end FLT.Mazur.GrassmannianChart
