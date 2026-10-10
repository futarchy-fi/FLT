/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalNodeFamily

/-!
# Actual containing charts for the fixed node family

The retained charts use the same equality transport as the node sections.
Their images are exactly those of the original global indexed atlas.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth)
local notation "K" => ResidueField R

/-- The original retained tensor chart with its target index written as the final stage. -/
def retainedTensorChartAt (t : ℕ) (ht : t ≤ n) (j : ℕ) (hj : j + 1 ≤ t) :=
  olderGlobalTensorChart hπ data K j (by omega) (t - (j + 1)) (by omega) ≫
    eqToHom (finiteGlobalTensorModel_index_congr hπ data K (by omega) ht (by omega))

/-- The fixed-stage spelling preserves the full original chart map. -/
theorem retainedTensorChartAt_original (j : ℕ) (hj : j + 1 ≤ n)
    (r : ℕ) (hr : j + 1 + r ≤ n) :
    retainedTensorChartAt hπ data (j + 1 + r) hr j (by omega) =
      olderGlobalTensorChart hπ data K j hj r hr := by
  apply eq_of_heq
  refine (comp_eqToHom_heq _ _).trans ?_
  congr 1
  · omega
  · apply proof_irrel_heq

/-- Every transported node still factors through its original full successive chart. -/
theorem retainedNodeSectionAt_range (t : ℕ) (ht : t ≤ n) (j : ℕ) (hj : j + 1 ≤ t)
    (hk : 2 * (start + j + 1) ≤ depth) (i : Fin 2) :
    Set.range (retainedNodeSectionAt hπ data D t ht j hj hk i) ⊆
      Set.range (retainedTensorChartAt hπ data t ht j hj) := by
  obtain ⟨r, he⟩ : ∃ r, t = j + 1 + r := ⟨t - (j + 1), by omega⟩
  subst t
  rw [retainedNodeSectionAt_original hπ data D j (by omega),
    retainedTensorChartAt_original hπ data j (by omega)]
  exact orderedRetainedSection_range hπ data D j (by omega) r ht hk i

/-- The entire fixed chart occupies its original reversed-depth global atlas index. -/
theorem retainedTensorChartAt_range_index (t : ℕ) (ht : t ≤ n)
    (j : ℕ) (hj : j + 1 ≤ t) :
    Set.range (retainedTensorChartAt hπ data t ht j hj) =
      Set.range (globalTensorAtlasMap hπ data K t ht ⟨t - j + 1, by omega⟩) := by
  obtain ⟨r, he⟩ : ∃ r, t = j + 1 + r := ⟨t - (j + 1), by omega⟩
  subst t
  rw [retainedTensorChartAt_original hπ data j (by omega)]
  have hi : (⟨j + 1 + r - j + 1, by omega⟩ : Fin (j + 1 + r + 3)) =
      Fin.succ ⟨r + 1, by omega⟩ := Fin.ext (by dsimp; omega)
  rw [hi, ← olderGlobalTensorChart_eq_index hπ data K j (by omega) r ht]
  exact (olderSuccessiveTensorAtlasIso hπ data K j (by omega) r ht).hom
    |>.homeomorph.surjective.range_comp
      (globalTensorAtlasMap hπ data K (j + 1 + r) ht (Fin.succ ⟨r + 1, by omega⟩))

end FLT.Mazur.WeierstrassDividedDepth
