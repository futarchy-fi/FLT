/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedEqualityNodeFamily

/-!
# Distinctness of the original equality-depth attachments

Chart exclusions separate all retained depths and the initial pair, without
requiring a split terminal node or a strict-depth hypothesis.
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
  (hk : 2 * (start + s + 1) ≤ depth)
local notation "N" => equalityNodeSection hπ data D s hs hk

/-- Attachments at different retained depths have disjoint original images. -/
theorem equalityNodeSection_levels_disjoint (a b : Fin (s + 1)) (hab : a < b)
    (i k : Fin 2) :
    Disjoint (Set.range (N (.inr (a, i)))) (Set.range (N (.inr (b, k)))) :=
  (retainedNodeSectionAt_later_disjoint hπ data D (s + 1) hs a.val b.val hab
    (by omega) (by omega) i).mono_right
      (retainedNodeSectionAt_range hπ data D (s + 1) hs b.val (by omega) (by omega) k)

/-- Distinct retained depths cannot represent the same section. -/
theorem equalityNodeSection_levels_ne (a b : Fin (s + 1)) (hab : a ≠ b) (i k : Fin 2) :
    N (.inr (a, i)) ≠ N (.inr (b, k)) := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact nodeMaps_ne_of_disjoint _ _
      (equalityNodeSection_levels_disjoint hπ data D s hs hk a b h i k)
  · exact (nodeMaps_ne_of_disjoint _ _
      (equalityNodeSection_levels_disjoint hπ data D s hs hk b a h k i)).symm

/-- Retained depth and tangent order together index the sections injectively. -/
theorem equalityNodeSection_retained_injective :
    Function.Injective (fun a : Fin (s + 1) × Fin 2 => N (.inr a)) := by
  rintro ⟨a, i⟩ ⟨b, k⟩ he
  have hab : a = b := by
    by_contra h
    exact equalityNodeSection_levels_ne hπ data D s hs hk a b h i k he
  subst b
  have hik : i = k := by
    fin_cases i <;> fin_cases k
    · rfl
    · exact (equalityNodeSection_retained_ne hπ data D s hs hk a he).elim
    · exact (equalityNodeSection_retained_ne hπ data D s hs hk a he.symm).elim
    · rfl
  subst k
  rfl

/-- The original initial pair misses all retained attachments at equality depth. -/
theorem equalityNodeSection_initial_retained_disjoint
    (a : {_i : Fin 2 // 0 < start}) (j : Fin (s + 1)) (b : Fin 2) :
    Disjoint (Set.range (N (.inl a))) (Set.range (N (.inr (j, b)))) :=
  orderedInitialSections_retained_disjoint hπ data D (s + 1) hs a.property j.val
    (by omega) (by omega) a.val b

/-- The two initial attachments retain their ordered distinction. -/
theorem equalityNodeSection_initial_injective :
    Function.Injective (fun a : {_i : Fin 2 // 0 < start} => N (.inl a)) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ he
  apply Subtype.ext
  fin_cases a <;> fin_cases b
  · rfl
  · exact (initialGlobalSections_ne hπ data D (s + 1) hs ha (by omega) he).elim
  · exact (initialGlobalSections_ne hπ data D (s + 1) hs ha (by omega) he.symm).elim
  · rfl

/-- Every original attachment has a unique index, with no strict-depth assumption. -/
theorem equalityNodeSection_injective : Function.Injective N := by
  rintro (a | a) (b | b) he
  · exact congrArg Sum.inl (equalityNodeSection_initial_injective hπ data D s hs hk he)
  · exact (nodeMaps_ne_of_disjoint _ _
      (equalityNodeSection_initial_retained_disjoint hπ data D s hs hk a b.1 b.2) he).elim
  · exact (nodeMaps_ne_of_disjoint _ _
      (equalityNodeSection_initial_retained_disjoint hπ data D s hs hk b a.1 a.2) he.symm).elim
  · exact congrArg Sum.inr (equalityNodeSection_retained_injective hπ data D s hs hk he)

/-- Keeping the coefficient structure preserves injective indexing of the actual sections. -/
theorem equalityNodeOverSection_injective :
    Function.Injective (equalityNodeOverSection hπ data D s hs hk) := by
  intro a b he
  exact equalityNodeSection_injective hπ data D s hs hk (congrArg Over.Hom.left he)

end FLT.Mazur.WeierstrassDividedDepth
