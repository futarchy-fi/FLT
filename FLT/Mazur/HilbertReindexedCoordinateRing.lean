/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertComplementCoordinateRing

/-!
# Closed Hilbert chart maps with any complementary index

A bijection of the complementary monomials with a fixed index only renames
polynomial variables. The resulting coordinate map is still surjective onto
the entire original Hilbert chart ring, and its spectrum map is closed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
set_option backward.isDefEq.respectTransparency false
universe u
variable (R I : Type u) [CommRing R] (d : ℕ)
  (m : Fin d → BoundedHilbertMonomials I d)
  {κ : Type u} (e : HilbertComplementMonomials I d m ≃ κ)

/-- Reindexed matrix entries in the full original universal quotient. -/
def chartReindexedCoordinateMap :
    MvPolynomial (Fin d × κ) R →ₐ[R]
      ChartRing R I d (fun a ↦ MvPolynomial.monomial (m a).val 1) :=
  MvPolynomial.aeval fun kj ↦ chartBoundedCoordinate R I d
    (fun a ↦ MvPolynomial.monomial (m a).val 1) kj.1 (e.symm kj.2).val

/-- Reading a renamed generator gives its original complementary monomial column. -/
theorem chartReindexedCoordinateMap_X (k : Fin d) (j : κ) :
    chartReindexedCoordinateMap R I d m e (MvPolynomial.X (k, j)) =
      chartBoundedCoordinate R I d (fun a ↦ MvPolynomial.monomial (m a).val 1)
        k (e.symm j).val := MvPolynomial.aeval_X _ _

/-- Renaming complementary generators recovers the original coefficient map. -/
theorem chartReindexedCoordinateMap_factor :
    (chartReindexedCoordinateMap R I d m e).comp
        (MvPolynomial.rename (fun kn : Fin d × HilbertComplementMonomials I d m ↦
          (kn.1, e kn.2))) = chartComplementCoordinateMap R I d m := by
  apply MvPolynomial.algHom_ext
  rintro ⟨k, n⟩
  simp only [AlgHom.comp_apply, MvPolynomial.rename_X, chartReindexedCoordinateMap_X,
    Equiv.symm_apply_apply, chartComplementCoordinateMap, MvPolynomial.aeval_X]

/-- The reindexed parameters generate the entire original chart, with all equations retained. -/
theorem chartReindexedCoordinateMap_surjective :
    Function.Surjective (chartReindexedCoordinateMap R I d m e) := by
  have h := chartComplementCoordinateMap_surjective R I d m
  rw [← chartReindexedCoordinateMap_factor R I d m e] at h
  exact Function.Surjective.of_comp h

/-- The closed Hilbert chart morphism into the fixed complementary matrix scheme. -/
def hilbertReindexedChartMap :
    Spec (.of (ChartRing R I d (fun a ↦ MvPolynomial.monomial (m a).val 1))) ⟶
      GrassmannianChart.splitChartScheme R κ d :=
  Spec.map (CommRingCat.ofHom (chartReindexedCoordinateMap R I d m e).toRingHom)

instance hilbertReindexedChartMap_isClosedImmersion :
    IsClosedImmersion (hilbertReindexedChartMap R I d m e) :=
  IsClosedImmersion.spec_of_surjective _ (chartReindexedCoordinateMap_surjective R I d m e)

/-- The reindexed closed map remains over the original coefficient spectrum. -/
theorem hilbertReindexedChartMap_over :
    hilbertReindexedChartMap R I d m e ≫ GrassmannianChart.splitChartStructure R κ d =
      Spec.algebraMap R (ChartRing R I d (fun a ↦ MvPolynomial.monomial (m a).val 1)) := by
  rw [hilbertReindexedChartMap, GrassmannianChart.splitChartStructure,
    Spec.algebraMap, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (AlgHom.comp_algebraMap (chartReindexedCoordinateMap R I d m e))

/-- Identity reindexing is the previously constructed complementary chart map. -/
theorem hilbertReindexedChartMap_refl :
    hilbertReindexedChartMap R I d m (Equiv.refl _) = hilbertComplementChartMap R I d m := rfl

end FLT.Mazur.HilbertChart
