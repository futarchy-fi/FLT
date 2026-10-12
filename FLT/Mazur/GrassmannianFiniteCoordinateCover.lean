/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianFiniteCoordinateCharts
public import FLT.Mazur.GrassmannianDeterminantSectionLoci

/-!
# A finite coordinate cover and compactness of the original Grassmannian

The same finitely many original-base column selections cover every polynomial
chart prime. Their chart images are affine, so the entire glued scheme is compact.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M ι κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)
local notation "G" => ambientGrassmannianScheme R M κ d
local notation "chart" => ambientGrassmannianChart R M κ d

/-- At each prime of every original chart some selected-coordinate determinant is nonzero. -/
theorem exists_finiteCoordinateChart_det_notMem (i : AmbientChartIndex R M κ d)
    (p : PrimeSpectrum (MvPolynomial (Fin d × κ) R)) :
    ∃ a : Fin d ↪ ι, determinantChartSection i (finiteCoordinateChart b hκ a) ∉ p.asIdeal := by
  let A := Localization.AtPrime p.asIdeal
  let f : MvPolynomial (Fin d × κ) R →ₐ[R] A := IsScalarTower.toAlgHom R _ A
  let N := ambientChartPointOfSplit (ambientChartBaseChange A i)
    (splitChartPolynomialEquiv R A κ d f)
  obtain ⟨a, ha⟩ := exists_finiteCoordinateChart_local b hκ i N
  have hu := (ambientChartPolynomial_second_iff i (finiteCoordinateChart b hκ a) f).mp ha
  exact ⟨a, (IsLocalization.AtPrime.isUnit_to_map_iff A p.asIdeal _).mp hu⟩

/-- Every point of the original scheme lies in one of the finitely indexed coordinate charts. -/
theorem finiteCoordinateChart_cover (x : G) :
    ∃ a : Fin d ↪ ι, x ∈ (chart (finiteCoordinateChart b hκ a)).opensRange := by
  obtain ⟨i, p, rfl⟩ := ambientGrassmannianChart_cover R M κ d x
  obtain ⟨a, ha⟩ := exists_finiteCoordinateChart_det_notMem b hκ i p
  refine ⟨a, ?_⟩
  change p ∈ chart i ⁻¹ᵁ (chart (finiteCoordinateChart b hκ a)).opensRange
  rw [determinantChartSection_basicOpen]
  exact ha

/-- The finite coordinate-chart images cover the whole Grassmannian as opens. -/
theorem finiteCoordinateChart_iSup :
    (⨆ a : Fin d ↪ ι, (chart (finiteCoordinateChart b hκ a)).opensRange) = ⊤ := by
  apply top_unique
  intro x _
  exact Opens.mem_iSup.mpr (finiteCoordinateChart_cover b hκ x)

include b hκ in
/-- Actual finitely many affine chart images prove compactness without any projectivity premise. -/
theorem ambientGrassmannian_compactSpace : CompactSpace G := by
  classical
  apply isCompact_univ_iff.mp
  have hc := isCompact_iUnion (fun a : Fin d ↪ ι ↦
    (isAffineOpen_opensRange (chart (finiteCoordinateChart b hκ a))).isCompact)
  have he : (⋃ a : Fin d ↪ ι,
      ((chart (finiteCoordinateChart b hκ a)).opensRange : Set G)) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact finiteCoordinateChart_cover b hκ x
  rwa [he] at hc

end FLT.Mazur.GrassmannianChart
