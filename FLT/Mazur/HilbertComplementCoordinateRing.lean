/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundedNormalizedCoordinates
public import FLT.Mazur.GrassmannianSplitChartScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed Hilbert chart maps using only complementary matrix entries

Selected columns are fixed identity entries, so the remaining bounded columns
alone generate the entire original Hilbert chart ring. This constructs closed
maps into split Grassmannian coordinate schemes over the original base. The
ambient decomposition and global pullback identification are separate work.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
set_option backward.isDefEq.respectTransparency false
universe u
variable (R I : Type u) [CommRing R] (d : ℕ)
  (m : Fin d → BoundedHilbertMonomials I d)

/-- The actual bounded monomial columns outside the selected tuple. -/
def HilbertComplementMonomials :=
  {n : BoundedHilbertMonomials I (d + 1) //
    n ∉ Set.range (boundedSelectedMonomial I d m)}

/-- The complementary Grassmannian coordinates in the original universal Hilbert quotient. -/
def chartComplementCoordinateMap :
    MvPolynomial (Fin d × HilbertComplementMonomials I d m) R →ₐ[R]
      ChartRing R I d (fun a ↦ MvPolynomial.monomial (m a).val 1) :=
  MvPolynomial.aeval fun kn ↦ chartBoundedCoordinate R I d
    (fun a ↦ MvPolynomial.monomial (m a).val 1) kn.1 kn.2.val

/-- Insert the fixed identity entries into the complete bounded matrix. -/
def boundedToComplementCoordinates : BoundedCoordinateRing R I d →ₐ[R]
    MvPolynomial (Fin d × HilbertComplementMonomials I d m) R := by
  classical
  exact MvPolynomial.aeval fun kn ↦
    if h : kn.2 ∈ Set.range (boundedSelectedMonomial I d m) then
      if Classical.choose h = kn.1 then 1 else 0
    else MvPolynomial.X (kn.1, ⟨kn.2, h⟩)

/-- Restoring identity columns recovers every original bounded-coordinate parameter. -/
theorem chartComplementCoordinateMap_factor :
    (chartComplementCoordinateMap R I d m).comp (boundedToComplementCoordinates R I d m) =
      chartBoundedCoordinateMap R I d (fun a ↦ MvPolynomial.monomial (m a).val 1) := by
  classical
  apply MvPolynomial.algHom_ext
  rintro ⟨k, n⟩
  simp only [AlgHom.comp_apply, boundedToComplementCoordinates, MvPolynomial.aeval_X]
  split_ifs with h hkn
  · rw [map_one, chartBoundedCoordinateMap_X, ← Classical.choose_spec h,
      chartBoundedCoordinate_selected, ite_eq_left hkn]
  · rw [map_zero, chartBoundedCoordinateMap_X, ← Classical.choose_spec h,
      chartBoundedCoordinate_selected, ite_eq_right hkn]
  · rw [chartComplementCoordinateMap, MvPolynomial.aeval_X, chartBoundedCoordinateMap_X]

/-- Complementary coordinates alone generate the whole original Hilbert chart ring. -/
theorem chartComplementCoordinateMap_surjective :
    Function.Surjective (chartComplementCoordinateMap R I d m) := by
  have h := chartBoundedCoordinateMap_surjective R I d
    (fun a ↦ MvPolynomial.monomial (m a).val 1)
    (fun a ↦ (MvPolynomial.totalDegree_monomial_le _ _).trans (m a).property)
  rw [← chartComplementCoordinateMap_factor] at h
  exact Function.Surjective.of_comp h

/-- The actual monomial Hilbert chart maps into the complementary matrix scheme. -/
def hilbertComplementChartMap :
    Spec (.of (ChartRing R I d (fun a ↦ MvPolynomial.monomial (m a).val 1))) ⟶
      GrassmannianChart.splitChartScheme R (HilbertComplementMonomials I d m) d :=
  Spec.map (CommRingCat.ofHom (chartComplementCoordinateMap R I d m).toRingHom)

/-- The constructed complementary matrix morphism is a closed immersion. -/
instance hilbertComplementChartMap_isClosedImmersion :
    IsClosedImmersion (hilbertComplementChartMap R I d m) :=
  IsClosedImmersion.spec_of_surjective _ (chartComplementCoordinateMap_surjective R I d m)

/-- The closed complementary-coordinate morphism preserves the original coefficient base. -/
theorem hilbertComplementChartMap_over :
    hilbertComplementChartMap R I d m ≫
        GrassmannianChart.splitChartStructure R (HilbertComplementMonomials I d m) d =
      Spec.algebraMap R (ChartRing R I d (fun a ↦ MvPolynomial.monomial (m a).val 1)) := by
  rw [hilbertComplementChartMap, GrassmannianChart.splitChartStructure,
    Spec.algebraMap, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (AlgHom.comp_algebraMap (chartComplementCoordinateMap R I d m))

end FLT.Mazur.HilbertChart
