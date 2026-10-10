/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalSections
public import FLT.Mazur.WeierstrassDividedAdjacentZeroSectionSeparation
public import FLT.Mazur.WeierstrassDividedAdjacentSectionSeparation

/-!
# One ordered pair of retained sections at every depth

The positive and zero-depth constructions are selected by their actual depth.
Both entries retain the original node origins and their order.
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
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n) (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R

/-- The two original retained nodes, uniformly including the scale-one chart. -/
def orderedRetainedSection (i : Fin 2) :
    Spec (.of K) ⟶ finiteGlobalTensorModel hπ data K (j + 1 + r) hr :=
  if h : 0 < start + j then
    Fin.cases (olderGlobalFirstSection hπ data D j hj r hr h hk)
      (fun _ => olderGlobalSecondSection hπ data D j hj r hr h hk) i
  else
    Fin.cases (olderGlobalZeroFirstSection hπ data D j hj r hr (by omega) hk)
      (fun _ => olderGlobalZeroSecondSection hπ data D j hj r hr (by omega) hk) i

/-- Positive-depth entries are exactly the established ordered middle-node sections. -/
theorem orderedRetainedSection_positive (h : 0 < start + j) (i : Fin 2) :
    orderedRetainedSection hπ data D j hj r hr hk i =
      Fin.cases (olderGlobalFirstSection hπ data D j hj r hr h hk)
        (fun _ => olderGlobalSecondSection hπ data D j hj r hr h hk) i := by
  simp only [orderedRetainedSection, dite_eq_left h]

/-- The zero-depth entries are exactly the original full-node sections. -/
theorem orderedRetainedSection_zero (h : start + j = 0) (i : Fin 2) :
    orderedRetainedSection hπ data D j hj r hr hk i =
      Fin.cases (olderGlobalZeroFirstSection hπ data D j hj r hr h hk)
        (fun _ => olderGlobalZeroSecondSection hπ data D j hj r hr h hk) i := by
  simp only [orderedRetainedSection, dite_eq_right (show ¬0 < start + j by omega)]

/-- The uniform pair never identifies its two entries. -/
theorem orderedRetainedSection_ne :
    orderedRetainedSection hπ data D j hj r hr hk 0 ≠
      orderedRetainedSection hπ data D j hj r hr hk 1 := by
  by_cases h : 0 < start + j
  · rw [orderedRetainedSection_positive hπ data D j hj r hr hk h,
      orderedRetainedSection_positive hπ data D j hj r hr hk h]
    exact olderGlobalSections_ne hπ data D j hj r hr h hk
  · rw [orderedRetainedSection_zero hπ data D j hj r hr hk (by omega),
      orderedRetainedSection_zero hπ data D j hj r hr hk (by omega)]
    exact olderGlobalZeroSections_ne hπ data D j hj r hr (by omega) hk

/-- Every entry belongs to its entire original successive chart. -/
theorem orderedRetainedSection_range (i : Fin 2) :
    Set.range (orderedRetainedSection hπ data D j hj r hr hk i) ⊆
      Set.range (olderGlobalTensorChart hπ data K j hj r hr) := by
  by_cases h : 0 < start + j
  · rw [orderedRetainedSection_positive hπ data D j hj r hr hk h]
    fin_cases i <;> rintro _ ⟨x, rfl⟩ <;> exact ⟨_, rfl⟩
  · rw [orderedRetainedSection_zero hπ data D j hj r hr hk (by omega)]
    rw [← olderGlobalZeroSuccessiveChart_range hπ data D j hj r hr (by omega) hk]
    fin_cases i <;> rintro _ ⟨x, rfl⟩ <;> exact ⟨_, rfl⟩

end FLT.Mazur.WeierstrassDividedDepth
