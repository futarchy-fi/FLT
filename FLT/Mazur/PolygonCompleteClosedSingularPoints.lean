/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedSmoothLocus
public import FLT.Mazur.PolygonOriginalNodePoint

/-!
# The only nonsmooth closed-fiber images are the specified complete nodes

The cartesian original stage detects smoothness. Its arithmetic node charts
have maximal coordinate ideals, so every nonsmooth stage point is the
specified coordinate origin and has the specified complete-node image.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local instance] exactVeroneseProjToBase_lfp

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Every actual original stage recovers the actual complete-family smooth locus. -/
theorem originalStage_preimage_smoothLocus (m : ℕ) :
    originalStageToCompatibleProj K n h m ⁻¹ᵁ
        (exactVeroneseProjToBase K n h).smoothLocus = (family K m n h).hom.smoothLocus := by
  let _ := exactVeroneseProjToBase_flat K n h
  let hp := originalStageToCompatibleProj_isPullback K n h m
  rw [← hp.isoPullback_hom_fst, Scheme.Hom.comp_preimage,
    Scheme.Hom.preimage_smoothLocus_baseChange, Scheme.Hom.preimage_smoothLocus_eq]
  congr 1
  exact hp.isoPullback_hom_snd

omit [NeZero n] in
/-- Every nonsmooth original stage point is one of its specified original nodes. -/
theorem originalStage_nonsmooth_eq_node (m : ℕ) (x : (family K m n h).left)
    (hx : x ∉ (family K m n h).hom.smoothLocus) :
    ∃ i, x = originalStageNode K n h m i := by
  obtain ⟨i, z, rfl⟩ := PolygonInfinitesimal.charts_cover (Ring K m) (parameter K m) n h x
  have hz : z ∉ (PolygonSmoothing.chartStructure (Ring K m) (parameter K m)).smoothLocus := by
    intro hz
    apply hx
    change z ∈ PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h i ⁻¹ᵁ
      (family K m n h).hom.smoothLocus
    rw [Scheme.Hom.preimage_smoothLocus_eq]
    change z ∈ (PolygonInfinitesimal.chart _ _ n h i ≫
      PolygonInfinitesimal.toBase _ _ n h).smoothLocus
    rw! [PolygonInfinitesimal.chart_toBase]
    exact hz
  have he := (stageNodeIdeal_isMaximal K m).eq_of_le z.isPrime.ne_top
    (PolygonSmoothing.coordinateIdeal_le_of_not_smooth _ z hz)
  have hz' : z = stageNodePoint K m := PrimeSpectrum.ext he.symm
  exact ⟨i, congrArg (PolygonInfinitesimal.chart _ _ n h i) hz'⟩

/-- A nonsmooth point from the actual closed fiber is a specified complete node. -/
theorem completeClosedFiber_nonsmooth_eq_node (x : PolygonCyclicAtlas.scheme K n h)
    (hx : completeClosedFiberInclusion K n h x ∉
      (exactVeroneseProjToBase K n h).smoothLocus) :
    ∃ i, completeClosedFiberInclusion K n h x = completeNode K n h i := by
  have hs : specialFiberInclusion K 0 n h x ∉ (family K 0 n h).hom.smoothLocus := by
    rw [← originalStage_preimage_smoothLocus K n h 0]
    exact hx
  obtain ⟨i, hi⟩ := originalStage_nonsmooth_eq_node K n h 0 _ hs
  exact ⟨i, congrArg (originalStageToCompatibleProj K n h 0) hi⟩

end FLT.Mazur.PolygonInfinitesimalStages
