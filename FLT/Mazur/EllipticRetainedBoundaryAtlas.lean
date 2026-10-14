/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteRetainedSpecialization
public import FLT.Mazur.WeierstrassDividedOlderResidueInfinity
public import FLT.Mazur.SchemeOpenChartRange

/-!
# The retained arithmetic boundary belongs to its original atlas member

The actual tensor boundary lies in the full retained successive chart.
At positive depth its entire image misses the infinity chart, independently
of arithmetic point lifting or a choice of Laurent coordinate.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (t : ℕ) (ht : j + 1 + t ≤ n)
  (S : Type u) [CommRing S] [Algebra A S]
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap A S))
local notation "f" => finiteGlobalStructure hπ data (j + 1 + t) ht
local notation "b" => finiteRetainedBoundaryTensorChart A hπ data j hj t ht S
local notation "c" => olderGlobalTensorChart hπ data S j hj t ht

/-- The full older global tensor chart is cartesian over its original integral chart. -/
theorem retainedBoundaryAtlas_isPullback :
    IsPullback c TensorOpenChart.projection (pullback.snd q f)
      (olderGlobalChart hπ data j hj t ht) :=
  (olderSuccessiveTensorChart_isPullback hπ data j hj t ht S).paste_horiz
    (finiteLocalTensorEmbedding_isPullback hπ data S (j + 1 + t) ht)

/-- The entire retained tensor boundary lies in its original successive atlas member. -/
theorem finiteRetainedBoundaryTensorChart_range_subset : Set.range b ⊆ Set.range c := by
  rw [SchemeOpenChartRange.range_of_isPullback _ _ _ _
    (retainedBoundaryAtlas_isPullback A hπ data j hj t ht S).flip]
  rintro z ⟨x, rfl⟩
  change pullback.snd q f (b x) ∈ Set.range (olderGlobalChart hπ data j hj t ht)
  have he := congrArg (fun g => g x) (TensorOpenChart.chart_snd f
    (finiteRetainedBoundaryChart A hπ data j hj t ht)
    (finiteRetainedBoundaryChart_algebra A hπ data j hj t ht) (S := S))
  rw [show pullback.snd q f (b x) =
    finiteRetainedBoundaryChart A hπ data j hj t ht (TensorOpenChart.projection x) from he]
  exact ⟨_, rfl⟩

/-- The original index of the whole retained boundary is preserved after coefficient extension. -/
theorem finiteRetainedBoundaryTensorChart_range_index :
    Set.range b ⊆ Set.range (globalTensorAtlasMap hπ data S (j + 1 + t) ht
      (Fin.succ ⟨t + 1, by omega⟩)) := by
  have h := finiteRetainedBoundaryTensorChart_range_subset A hπ data j hj t ht S
  rw [← olderGlobalTensorChart_eq_index hπ data S j hj t ht,
    SchemeOpenChartRange.range_iso_comp] at h
  exact h

variable {depth : ℕ} (D : SplitNodeDepth W π depth) (hk0 : 0 < start + j)

include D hk0 in
/-- The full positive-depth retained boundary is disjoint from the original infinity chart. -/
theorem finiteRetainedBoundaryTensorChart_infinity_disjoint :
    Disjoint (Set.range (finiteRetainedBoundaryTensorChart A hπ data j hj t ht (ResidueField A)))
      (Set.range (finiteInfinityTensorChart hπ data (ResidueField A) (j + 1 + t) ht)) := by
  apply (olderGlobalResidue_infinity_disjoint (ResidueField A) hπ data j hj t ht _ hk0).mono_left
    (finiteRetainedBoundaryTensorChart_range_subset A hπ data j hj t ht (ResidueField A))
  exact (residue_eq_zero_iff π).mpr
    (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)

end FLT.Mazur.WeierstrassDividedDepth
