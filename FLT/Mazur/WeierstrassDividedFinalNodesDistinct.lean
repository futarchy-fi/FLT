/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalInitialNodesDistinct

/-!
# All original final-stage node sections are pairwise distinct

The initial pair, every retained ordered pair, and the common terminal-branch
origin have one injective indexing. All separations follow from the actual charts.
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
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)

/-- The initial ordered subfamily keeps exactly its original two indices. -/
theorem finalNodeSection_initial_injective : Function.Injective
    (fun a : {_i : Fin 2 // 0 < start} =>
      finalNodeSection hπ data D s hs hk hp (.inl (.inl a))) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ he
  apply Subtype.ext
  fin_cases a <;> fin_cases b
  · rfl
  · exact (finalNodeSection_initial_ne hπ data D s hs hk hp ha he).elim
  · exact (finalNodeSection_initial_ne hπ data D s hs hk hp ha he.symm).elim
  · rfl

/-- Every original node section has a unique index in the fixed final-stage family. -/
theorem finalNodeSection_injective :
    Function.Injective (finalNodeSection hπ data D s hs hk hp) := by
  rintro ((a | a) | ⟨⟩) ((b | b) | ⟨⟩) he
  · exact congrArg (fun i => Sum.inl (Sum.inl i))
      (finalNodeSection_initial_injective hπ data D s hs hk hp he)
  · exact (nodeMaps_ne_of_disjoint _ _
      (finalNodeSection_initial_retained_disjoint hπ data D s hs hk hp a b.1 b.2) he).elim
  · exact (nodeMaps_ne_of_disjoint _ _
      (finalNodeSection_terminal_initial_disjoint hπ data D s hs hk hp a) he.symm).elim
  · exact (nodeMaps_ne_of_disjoint _ _
      (finalNodeSection_initial_retained_disjoint hπ data D s hs hk hp b a.1 a.2) he.symm).elim
  · exact congrArg (fun i => Sum.inl (Sum.inr i))
      (finalNodeSection_retained_injective hπ data D s hs hk hp he)
  · exact (finalNodeSection_terminal_retained_ne hπ data D s hs hk hp a.1 a.2 he.symm).elim
  · exact (nodeMaps_ne_of_disjoint _ _
      (finalNodeSection_terminal_initial_disjoint hπ data D s hs hk hp b) he).elim
  · exact (finalNodeSection_terminal_retained_ne hπ data D s hs hk hp b.1 b.2 he).elim
  · rfl

/-- Distinct fixed indices represent distinct original node sections. -/
theorem finalNodeSection_ne {a b : FinalNodeIndex start s} (h : a ≠ b) :
    finalNodeSection hπ data D s hs hk hp a ≠ finalNodeSection hπ data D s hs hk hp b :=
  fun he => h (finalNodeSection_injective hπ data D s hs hk hp he)

end FLT.Mazur.WeierstrassDividedDepth
