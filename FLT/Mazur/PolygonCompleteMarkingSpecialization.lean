/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBaseMarkings
public import FLT.Mazur.PolygonOriginalAdicRealization
public import FLT.Mazur.LocalBaseSectionDisjointness

/-!
# Closed specializations and disjointness of the complete markings

The closed point of the complete coefficient base is the actual image of the
original zeroth coefficient stage. The reconstructed markings retain the
distinct original closed points, so separatedness gives disjoint full sections.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K]

/-- The actual closed coefficient point maps to the closed point of the complete base. -/
theorem baseToSeries_stageBasePoint (m : ℕ) :
    baseToSeries K m (stageBasePoint K m) = closedPoint (PowerSeries K) := by
  have he : reductionBase K m ≫ baseToSeries K m =
      Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff : PowerSeries K →+* K)) := by
    rw [reductionBase, baseToSeries, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext f
    exact reduction_seriesToStage K m f
  change (reductionBase K m ≫ baseToSeries K m) (default : Spec (.of K)) = _
  rw [he]
  apply PrimeSpectrum.ext
  change RingHom.ker (PowerSeries.constantCoeff : PowerSeries K →+* K) = _
  exact PowerSeries.ker_coeff_eq_max_ideal

variable (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The complete marking specializes to the original closed-stage marked point. -/
theorem completeBaseMarking_closedPoint (i : Fin n) :
    completeBaseMarking K n h i (closedPoint (PowerSeries K)) =
      originalStageToCompatibleProj K n h 0 (marking K 0 n h i (stageBasePoint K 0)) := by
  rw [← baseToSeries_stageBasePoint K 0]
  exact congrArg (fun f : Spec (.of (Ring K 0)) ⟶ exactVeroneseProj K n h ↦
    f (stageBasePoint K 0)) (baseToSeries_completeBaseMarking K n h i 0)

/-- Distinct original labels give distinct closed specializations of the complete markings. -/
theorem completeBaseMarking_closedPoint_ne {i j : Fin n} (hij : i ≠ j) :
    completeBaseMarking K n h i (closedPoint (PowerSeries K)) ≠
      completeBaseMarking K n h j (closedPoint (PowerSeries K)) := by
  rw [completeBaseMarking_closedPoint, completeBaseMarking_closedPoint]
  let _ := originalStageToCompatibleProj_isClosedImmersion K n h 0
  intro he
  have hm := (originalStageToCompatibleProj K n h 0).isClosedEmbedding.injective he
  exact Set.disjoint_left.mp (markings_pairwise K 0 n h hij)
    ⟨stageBasePoint K 0, rfl⟩ ⟨stageBasePoint K 0, hm.symm⟩

/-- The actual complete-base sections have pairwise disjoint images. -/
theorem completeBaseMarkings_pairwise :
    Pairwise (fun i j ↦ Disjoint (Set.range (completeBaseMarking K n h i))
      (Set.range (completeBaseMarking K n h j))) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  intro i j hij
  exact LocalBaseSectionDisjointness.disjoint_of_closedPoint_ne
    (exactVeroneseProjToBase K n h) _ _ (completeBaseMarking_toBase K n h i)
    (completeBaseMarking_toBase K n h j) (completeBaseMarking_closedPoint_ne K n h hij)

end FLT.Mazur.PolygonInfinitesimalStages
