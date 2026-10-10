/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentZeroExteriorSeparation
public import FLT.Mazur.WeierstrassDividedFinalNodeNonadjacent
public import FLT.Mazur.WeierstrassDividedOlderResidueInfinity

/-!
# The original initial exterior line at a fixed final stage

The full affine line avoids all later retained charts. Positive retained charts
also avoid the unchanged infinity chart.
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

/-- The full original incidence line with its target index fixed. -/
def retainedZeroExteriorLineAt (t : ℕ) (ht : t ≤ n) (j : ℕ) (hj : j + 1 ≤ t)
    (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth) :=
  olderGlobalZeroIncidence hπ data D j (by omega) (t - (j + 1)) (by omega) hk0 hk ≫
    eqToHom (finiteGlobalTensorModel_index_congr hπ data K (by omega) ht (by omega))

/-- The original stage sum recovers the actual incidence immersion. -/
theorem retainedZeroExteriorLineAt_original (j : ℕ) (hj : j + 1 ≤ n)
    (r : ℕ) (hr : j + 1 + r ≤ n) (hk0 : start + j = 0)
    (hk : 2 * (start + j + 1) ≤ depth) :
    retainedZeroExteriorLineAt hπ data D (j + 1 + r) hr j (by omega) hk0 hk =
      olderGlobalZeroIncidence hπ data D j hj r hr hk0 hk := by
  apply eq_of_heq
  refine (comp_eqToHom_heq _ _).trans ?_
  congr 1
  · omega
  · apply proof_irrel_heq

/-- Equality transport keeps the entire original line at the new target spelling. -/
@[reassoc] theorem retainedZeroExteriorLineAt_index_transport {a b : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (he : a = b) (j : ℕ) (hj : j + 1 ≤ a)
    (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth) :
    retainedZeroExteriorLineAt hπ data D a ha j hj hk0 hk ≫
        eqToHom (finiteGlobalTensorModel_index_congr hπ data K ha hb he) =
      retainedZeroExteriorLineAt hπ data D b hb j (by omega) hk0 hk := by
  subst b
  simp only [eqToHom_refl, Category.comp_id]

/-- The fixed exterior line still lies in the whole original retained chart. -/
theorem retainedZeroExteriorLineAt_range (t : ℕ) (ht : t ≤ n) (j : ℕ)
    (hj : j + 1 ≤ t) (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth) :
    Set.range (retainedZeroExteriorLineAt hπ data D t ht j hj hk0 hk) ⊆
      Set.range (retainedTensorChartAt hπ data t ht j hj) := by
  obtain ⟨r, rfl⟩ : ∃ r, t = j + 1 + r := ⟨t - (j + 1), by omega⟩
  rw [retainedZeroExteriorLineAt_original hπ data D j (by omega),
    retainedTensorChartAt_original hπ data j (by omega)]
  rintro _ ⟨x, rfl⟩
  exact ⟨_, rfl⟩

/-- A stage equality changes no exterior line point or morphism. -/
theorem retainedZeroExteriorLineAt_heq (t : ℕ) (ht : t ≤ n) (j : ℕ)
    (hj : j + 1 ≤ t) (r : ℕ) (hr : j + 1 + r ≤ n) (he : j + 1 + r = t)
    (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth) :
    HEq (retainedZeroExteriorLineAt hπ data D t ht j hj hk0 hk)
      (olderGlobalZeroIncidence hπ data D j (by omega) r hr hk0 hk) := by
  subst t
  rw [retainedZeroExteriorLineAt_original hπ data D j (by omega)]

/-- The full incidence line misses the next retained chart in the fixed-stage model. -/
theorem retainedZeroExteriorLineAt_next_disjoint (t : ℕ) (ht : t ≤ n) (j : ℕ)
    (hj : j + 2 ≤ t) (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth) :
    Disjoint (Set.range (retainedZeroExteriorLineAt hπ data D t ht j (by omega) hk0 hk))
      (Set.range (retainedTensorChartAt hπ data t ht (j + 1) (by omega))) := by
  obtain ⟨r, rfl⟩ : ∃ r, t = j + 2 + r := ⟨t - (j + 2), by omega⟩
  rw [retainedTensorChartAt_original hπ data (j + 1) (by omega)]
  have H := retainedZeroExteriorLineAt_heq hπ data D (j + 2 + r) ht j (by omega)
    (r + 1) (by omega) (by omega) hk0 hk
  have he := eq_of_heq (H.trans
    (adjacentZeroExteriorLine_original hπ data D j (by omega) hk0 hk r ht))
  rw [he]
  exact adjacentZeroExteriorLine_next_disjoint hπ data D j (by omega) hk0 hk r ht (by omega)

/-- Every later full retained chart misses the original initial exterior line. -/
theorem retainedZeroExteriorLineAt_later_disjoint (t : ℕ) (ht : t ≤ n) (a b : ℕ)
    (hab : a < b) (hb : b + 1 ≤ t) (hk0 : start + a = 0)
    (hk : 2 * (start + a + 1) ≤ depth) :
    Disjoint (Set.range (retainedZeroExteriorLineAt hπ data D t ht a (by omega) hk0 hk))
      (Set.range (retainedTensorChartAt hπ data t ht b hb)) := by
  by_cases he : b = a + 1
  · subst b
    exact retainedZeroExteriorLineAt_next_disjoint hπ data D t ht a (by omega) hk0 hk
  · exact (retainedTensorChartAt_nonadjacent_disjoint hπ data D t ht a b
      (by omega) hb).mono_left
      (retainedZeroExteriorLineAt_range hπ data D t ht a (by omega) hk0 hk)

include D in
/-- Every positive-depth retained chart misses the unchanged original infinity chart. -/
theorem retainedTensorChartAt_infinity_disjoint (t : ℕ) (ht : t ≤ n) (j : ℕ)
    (hj : j + 1 ≤ t) (hpos : 0 < start + j) :
    Disjoint (Set.range (retainedTensorChartAt hπ data t ht j hj))
      (Set.range (finiteInfinityTensorChart hπ data K t ht)) := by
  obtain ⟨r, rfl⟩ : ∃ r, t = j + 1 + r := ⟨t - (j + 1), by omega⟩
  rw [retainedTensorChartAt_original hπ data j (by omega)]
  apply olderGlobalResidue_infinity_disjoint K hπ data j (by omega) r ht _ hpos
  exact (residue_eq_zero_iff π).mpr
    (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)

end FLT.Mazur.WeierstrassDividedDepth
