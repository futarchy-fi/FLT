/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentEndpointRanges
public import FLT.Mazur.WeierstrassDividedRetainedLineSeparation

/-!
# Exact intersections between complete retained projective components

At successive levels only matching branches meet, at their original common node.
At greater distances the complete component images are disjoint.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
/-- A composite image lies in the image of its final map. -/
theorem componentRange_comp_subset {A B X : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ X) :
    Set.range (f ≫ g) ⊆ Set.range g := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f x, rfl⟩

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth)

/-- An ordered node belongs to the matching original full horizontal line. -/
theorem retainedNodeSectionAt_range_line (t : ℕ) (ht : t ≤ n) (j : ℕ)
    (hj : j + 1 ≤ t) (hk0 : 0 < start + j)
    (hk : 2 * (start + j + 1) ≤ depth) (i : Fin 2) :
    Set.range (retainedNodeSectionAt hπ data D t ht j hj hk i) ⊆
      Set.range (retainedLineAt hπ data D t ht j hj hk0 hk i) := by
  rw [← retainedLineAt_origin hπ data D t ht j hj hk0 hk i]
  exact componentRange_comp_subset _ _

/-- The opposite ordered node misses the entire horizontal line. -/
theorem retainedLineAt_cross_node_disjoint (t : ℕ) (ht : t ≤ n) (j : ℕ)
    (hj : j + 1 ≤ t) (hk0 : 0 < start + j)
    (hk : 2 * (start + j + 1) ≤ depth) (i k : Fin 2) (hik : i ≠ k) :
    Disjoint (Set.range (retainedLineAt hπ data D t ht j hj hk0 hk i))
      (Set.range (retainedNodeSectionAt hπ data D t ht j hj hk k)) := by
  have h : Disjoint (Set.range (retainedLineAt hπ data D t ht j hj hk0 hk i))
      (Set.range (retainedLineAt hπ data D t ht j hj hk0 hk k)) := by
    fin_cases i <;> fin_cases k
    · exact (hik rfl).elim
    · exact retainedLineAt_disjoint hπ data D t ht j hj hk0 hk
    · exact (retainedLineAt_disjoint hπ data D t ht j hj hk0 hk).symm
    · exact (hik rfl).elim
  exact h.mono_right (retainedNodeSectionAt_range_line hπ data D t ht j hj hk0 hk k)

/-- Equal level indices give the same original fixed-stage line. -/
theorem retainedLineAt_level_congr (t : ℕ) (ht : t ≤ n) {a b : ℕ}
    (ha : a + 1 ≤ t) (hb : b + 1 ≤ t) (hpa : 0 < start + a) (hpb : 0 < start + b)
    (hka : 2 * (start + a + 1) ≤ depth) (hkb : 2 * (start + b + 1) ≤ depth)
    (he : a = b) (i : Fin 2) :
    retainedLineAt hπ data D t ht a ha hpa hka i =
      retainedLineAt hπ data D t ht b hb hpb hkb i := by
  subst b
  rfl

variable (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + s + 1) ≤ depth)

/-- Two increasing complete components can meet only on the later component's zero node. -/
theorem finalAdjacentComponents_range_inter_reduce (a b : Fin s) (hab : a < b)
    (i k : Fin 2) :
    Set.range (finalAdjacentComponent hπ data D s hs hk a i) ∩
        Set.range (finalAdjacentComponent hπ data D s hs hk b k) =
      Set.range (retainedLineAt hπ data D (s + 1) hs (a.val + 1)
        (by omega) (by omega) (by omega) i) ∩
      Set.range (retainedNodeSectionAt hπ data D (s + 1) hs b.val
        (by omega) (by omega) k) := by
  rw [finalAdjacentComponent_range_line_node, finalAdjacentComponent_range_line_node]
  rw [Set.union_comm (Set.range (retainedLineAt _ _ _ _ _ _ _ _ _ _))]
  apply componentRange_union_inter
  · exact (retainedNodeSectionAt_later_disjoint hπ data D (s + 1) hs a.val
      (b.val + 1) (by omega) (by omega) (by omega) i).mono_right
      (retainedLineAt_range hπ data D (s + 1) hs (b.val + 1)
        (by omega) (by omega) (by omega) k)
  · exact (retainedNodeSectionAt_later_disjoint hπ data D (s + 1) hs a.val
      b.val hab (by omega) (by omega) i).mono_right
      (retainedNodeSectionAt_range hπ data D (s + 1) hs b.val (by omega) (by omega) k)
  · exact (retainedLineAt_later_disjoint hπ data D (s + 1) hs (a.val + 1)
      (b.val + 1) (by omega) (by omega) (by omega) (by omega) i).mono_right
      (retainedLineAt_range hπ data D (s + 1) hs (b.val + 1)
        (by omega) (by omega) (by omega) k)

/-- Matching successive complete components meet exactly at the original retained node. -/
theorem finalAdjacentComponents_successive_range_inter (a b : Fin s)
    (hab : b.val = a.val + 1) (i : Fin 2) :
    Set.range (finalAdjacentComponent hπ data D s hs hk a i) ∩
        Set.range (finalAdjacentComponent hπ data D s hs hk b i) =
      Set.range (retainedNodeSectionAt hπ data D (s + 1) hs b.val
        (by omega) (by omega) i) := by
  rw [finalAdjacentComponents_range_inter_reduce hπ data D s hs hk a b (by omega)]
  have hpos : 0 < start + b.val := by omega
  have H := retainedNodeSectionAt_range_line hπ data D (s + 1) hs b.val
    (by omega) hpos (by omega) i
  rw [retainedLineAt_level_congr hπ data D (s + 1) hs
    (b := b.val) _ (by omega) _ hpos _ (by omega) hab.symm i]
  exact Set.inter_eq_right.mpr H

/-- Crossed branches at successive retained levels have no common point. -/
theorem finalAdjacentComponents_successive_cross_disjoint (a b : Fin s)
    (hab : b.val = a.val + 1) (i k : Fin 2) (hik : i ≠ k) :
    Disjoint (Set.range (finalAdjacentComponent hπ data D s hs hk a i))
      (Set.range (finalAdjacentComponent hπ data D s hs hk b k)) := by
  apply Set.disjoint_iff_inter_eq_empty.mpr
  rw [finalAdjacentComponents_range_inter_reduce hπ data D s hs hk a b (by omega)]
  have hpos : 0 < start + b.val := by omega
  have H := retainedLineAt_cross_node_disjoint hπ data D (s + 1) hs b.val
    (by omega) hpos (by omega) i k hik
  rw [retainedLineAt_level_congr hπ data D (s + 1) hs
    (b := b.val) _ (by omega) _ hpos _ (by omega) hab.symm i]
  exact Set.disjoint_iff_inter_eq_empty.mp H

/-- Nonadjacent complete retained components have no common point, in either branch. -/
theorem finalAdjacentComponents_nonadjacent_disjoint (a b : Fin s)
    (hab : a.val + 2 ≤ b.val) (i k : Fin 2) :
    Disjoint (Set.range (finalAdjacentComponent hπ data D s hs hk a i))
      (Set.range (finalAdjacentComponent hπ data D s hs hk b k)) := by
  apply Set.disjoint_iff_inter_eq_empty.mpr
  rw [finalAdjacentComponents_range_inter_reduce hπ data D s hs hk a b (by omega)]
  exact Set.disjoint_iff_inter_eq_empty.mp
    ((retainedLineAt_later_disjoint hπ data D (s + 1) hs (a.val + 1) b.val
      (by omega) (by omega) (by omega) (by omega) i).mono_right
      (retainedNodeSectionAt_range hπ data D (s + 1) hs b.val (by omega) (by omega) k))

end FLT.Mazur.WeierstrassDividedDepth
