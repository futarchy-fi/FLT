/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroSplitCycleIntersections
public import FLT.Mazur.WeierstrassDividedZeroSplitCycleSeparation
public import FLT.Mazur.WeierstrassDividedZeroSplitCycleCoverage

/-!
# Complete point identifications for the actual cyclic normalization

The original special fiber is covered by the complete cyclic components.
Their only point identifications are equality within a component and the
specified zero/infinity markings across an edge. This is a statement about
points; the scheme pushout requires a separate descent argument.
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
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "Z" => zeroSplitCycleComponent hπ data D s hs hstart hk hp
local notation "C" => finalBranchComponent hπ data D s hs hk hp
local notation "N" => finalNodeOverSection hπ data D s hs hk hp

/-- Exact equality relation on the disjoint family of complete cyclic component points. -/
theorem zeroSplitCycleComponent_eq_iff (a b : Fin (2 * s + 3))
    (x y : ProjectiveLine.scheme K) :
    (Z a).left x = (Z b).left y ↔
      (a = b ∧ x = y) ∨
      (PolygonPinching.next (by omega) a = b ∧
        ∃ z : Spec (.of K), ProjectiveLine.zero K z = x ∧
          ProjectiveLine.infinity K z = y) ∨
      (PolygonPinching.next (by omega) b = a ∧
        ∃ z : Spec (.of K), ProjectiveLine.infinity K z = x ∧
          ProjectiveLine.zero K z = y) := by
  constructor
  · intro he
    by_cases hab : a = b
    · subst b
      exact Or.inl ⟨rfl,
        zeroSplitCycleComponent_point_injective hπ data D s hs hk hp hstart a he⟩
    · by_cases hn : PolygonPinching.next (by omega) a = b
      · refine Or.inr (Or.inl ⟨hn, ?_⟩)
        subst b
        exact (zeroSplitCycleComponent_next_eq_iff hπ data D s hs hstart hk hp a x y).mp he
      · by_cases hp' : PolygonPinching.next (by omega) b = a
        · refine Or.inr (Or.inr ⟨hp', ?_⟩)
          subst a
          obtain ⟨z, hz, hz'⟩ :=
            (zeroSplitCycleComponent_next_eq_iff hπ data D s hs hstart hk hp b y x).mp he.symm
          exact ⟨z, hz', hz⟩
        · exact False.elim (Set.disjoint_left.mp
            (zeroSplitCycleComponent_nonadjacent_disjoint hπ data D s hs hstart hk hp
              a b hab hn hp') ⟨x, rfl⟩ ⟨y, he.symm⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨hn, hxy⟩ | ⟨hp', z, hx, hy⟩)
    · rfl
    · subst b
      exact (zeroSplitCycleComponent_next_eq_iff hπ data D s hs hstart hk hp a x y).mpr hxy
    · subst a
      exact ((zeroSplitCycleComponent_next_eq_iff hπ data D s hs hstart hk hp b y x).mpr
        ⟨z, hy, hx⟩).symm

/-- A distinct intersecting component is necessarily one of the two cyclic neighbors. -/
theorem zeroSplitCycleComponent_intersecting_indices (a b : Fin (2 * s + 3))
    (h : (Set.range (Z a).left ∩ Set.range (Z b).left).Nonempty) :
    a = b ∨ PolygonPinching.next (by omega) a = b ∨
      PolygonPinching.next (by omega) b = a := by
  obtain ⟨_, ⟨x, hx⟩, ⟨y, hy⟩⟩ := h
  rcases (zeroSplitCycleComponent_eq_iff hπ data D s hs hstart hk hp a b x y).mp
      (hx.trans hy.symm) with h | h | h
  · exact Or.inl h.1
  · exact Or.inr (Or.inl h.1)
  · exact Or.inr (Or.inr h.1)

end FLT.Mazur.WeierstrassDividedDepth
