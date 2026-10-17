/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNodeIdealSheafDetection
public import FLT.Mazur.PolygonOneGonContractionFiberCharts
public import FLT.Mazur.IdealSheafOpenCoverDetection

/-!
# Normalization detects ideals of the collapsed chain

An ideal zero on every omitted component is determined by its restriction to
the retained component. At every node at least one complete branch is omitted,
so full node-ideal detection applies, including in the two-gon.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonCollapsedIdealDetection
open PolygonCyclicAtlas PolygonOneGonContraction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) (i : Fin n)

/-- Full ideals zero on the omitted components are detected on the retained normalization. -/
theorem ideal_ext {I J : (scheme K n h).IdealSheafData}
    (hI : ∀ j, j ≠ i → I.comap (componentMap K n h j) = ⊥)
    (hJ : ∀ j, j ≠ i → J.comap (componentMap K n h j) = ⊥)
    (hi : I.comap (componentMap K n h i) = J.comap (componentMap K n h i)) : I = J := by
  have hc (j : Fin n) : I.comap (componentMap K n h j) =
      J.comap (componentMap K n h j) := by
    by_cases hj : j = i
    · simpa only [hj] using hi
    · rw [hI j hj, hJ j hj]
  apply BaseAdicThickening.idealSheaf_ext_of_openCover
    (PolygonCyclicNormalizationFinite.targetCover K n h)
  intro j
  change I.comap (chart K n h j) = J.comap (chart K n h j)
  have hs : secondBranch K ≫ chart K n h j =
      ProjectiveLine.right K ≫ componentMap K n h (finRotate n j) := by
    simp only [right_componentMap, Equiv.symm_apply_apply]
  by_cases hj : j = i
  · have hn : finRotate n j ≠ i := by
      rw [← hj]
      exact (PolygonCyclicNormalizationPullback.successor_ne n h j).symm
    apply PolygonNodeIdealSheafDetection.eq_of_second_zero K
    · rw [← Scheme.IdealSheafData.comap_comp]
      rw [hs]
      rw [Scheme.IdealSheafData.comap_comp, hI _ hn, Scheme.IdealSheafData.comap_bot]
    · rw [← Scheme.IdealSheafData.comap_comp]
      rw [hs]
      rw [Scheme.IdealSheafData.comap_comp, hJ _ hn, Scheme.IdealSheafData.comap_bot]
    · rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
        ← left_componentMap, Scheme.IdealSheafData.comap_comp,
        Scheme.IdealSheafData.comap_comp, hc]
  · apply PolygonNodeIdealSheafDetection.eq_of_first_zero K
    · rw [← Scheme.IdealSheafData.comap_comp, ← left_componentMap,
        Scheme.IdealSheafData.comap_comp, hI j hj, Scheme.IdealSheafData.comap_bot]
    · rw [← Scheme.IdealSheafData.comap_comp, ← left_componentMap,
        Scheme.IdealSheafData.comap_comp, hJ j hj, Scheme.IdealSheafData.comap_bot]
    · rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
      rw [hs]
      rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, hc]

end FLT.Mazur.PolygonCollapsedIdealDetection
