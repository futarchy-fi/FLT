/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalNodeNonadjacent

/-!
# Pairwise distinct retained nodes in the final family

Chart exclusions separate different depths. The original ordered incidence
points separate the two entries at each depth, including scale one.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- Disjoint scheme-map images cannot give equal maps from a nonempty scheme. -/
theorem nodeMaps_ne_of_disjoint {X Y : Scheme.{u}} [Nonempty X] (f g : X ⟶ Y)
    (h : Disjoint (Set.range f) (Set.range g)) : f ≠ g := by
  intro he
  obtain ⟨x⟩ := ‹Nonempty X›
  exact Set.disjoint_left.mp h ⟨x, rfl⟩ ⟨x, congrArg (fun k => k x) he.symm⟩

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)

/-- No retained node at one depth equals any retained node at another depth. -/
theorem finalNodeSection_levels_ne (a b : Fin (s + 1)) (hab : a ≠ b) (i k : Fin 2) :
    finalNodeSection hπ data D s hs hk hp (.inl (.inr (a, i))) ≠
      finalNodeSection hπ data D s hs hk hp (.inl (.inr (b, k))) := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact nodeMaps_ne_of_disjoint _ _
      (finalNodeSection_levels_disjoint hπ data D s hs hk hp a b h i k)
  · exact (nodeMaps_ne_of_disjoint _ _
      (finalNodeSection_levels_disjoint hπ data D s hs hk hp b a h k i)).symm

/-- The complete retained subfamily is injectively indexed by depth and original order. -/
theorem finalNodeSection_retained_injective : Function.Injective
    (fun a : Fin (s + 1) × Fin 2 =>
      finalNodeSection hπ data D s hs hk hp (.inl (.inr a))) := by
  rintro ⟨a, i⟩ ⟨b, k⟩ he
  have hab : a = b := by
    by_contra h
    exact finalNodeSection_levels_ne hπ data D s hs hk hp a b h i k he
  subst b
  have hik : i = k := by
    fin_cases i <;> fin_cases k
    · rfl
    · exact (finalNodeSection_retained_ne hπ data D s hs hk hp a he).elim
    · exact (finalNodeSection_retained_ne hπ data D s hs hk hp a he.symm).elim
    · rfl
  subst k
  rfl

end FLT.Mazur.WeierstrassDividedDepth
