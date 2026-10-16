/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLabeledAtlas
public import FLT.Mazur.WeierstrassDividedArithmeticEarlierTerminal

/-!
# Earlier labeled charts miss the full arithmetic terminal node

The indexed nonadjacency theorem transports to both initial labels and to
every retained label except the last one. The original chart maps are used.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (k : ℕ) (hk : k ≤ n)
local notation "c" => arithmeticLabeledAtlasMap hπ data H m k hk
local notation "t" => arithmeticTensorAtlasMap hπ data m k hk

/-- Each full initial label is contained in the exact final indexed arithmetic chart. -/
theorem arithmeticLabeledAtlas_initial_range_subset (b : Bool) :
    Set.range (c (.initial b)) ⊆ Set.range (t (Fin.succ ⟨k + 1, by omega⟩)) := by
  rw [← arithmeticTensorAtlas_initial_range,
    ← arithmeticLabeledInitialChart_image hπ data H m k hk]
  cases b
  · exact Set.subset_union_left
  · exact Set.subset_union_right

/-- Each retained label is contained in its precise reverse-depth indexed arithmetic chart. -/
theorem arithmeticLabeledAtlas_retained_range_subset (a : Fin k) (b : Bool) :
    Set.range (c (.retained a b)) ⊆ Set.range (t (Fin.succ ⟨k - a.val, by omega⟩)) := by
  rw [← arithmeticRetainedTensorChart_range hπ data m k hk a.val a.isLt,
    ← arithmeticLabeledRetainedChart_image hπ data H m k hk a]
  cases b
  · exact Set.subset_union_left
  · exact Set.subset_union_right

/-- The normalized terminal label keeps exactly the full original terminal tensor image. -/
theorem arithmeticLabeledAtlas_terminal_range :
    Set.range (c .terminal) = Set.range (finiteArithmeticDividedTensorChart hπ data m k hk) :=
  arithmeticLabeledTerminalChart_image hπ data H m k hk

/-- The nonadjacent terminal exclusion uses the fixed arithmetic indexed maps. -/
theorem arithmeticTensorAtlas_earlier_terminal_disjoint (i : Fin (k + 3)) (hi : 3 ≤ i.val) :
    Disjoint (Set.range (t i))
      (Set.range (finiteArithmeticDividedTensorChart hπ data m k hk)) :=
  earlierArithmeticTensor_terminal_disjoint hπ data m k hk i hi

attribute [local irreducible] arithmeticLabeledAtlasMap arithmeticTensorAtlasMap
  finiteArithmeticDividedTensorChart

/-- At positive retention both complete initial labels miss the normalized terminal node. -/
theorem arithmeticLabeledAtlas_initial_terminal_disjoint (hpos : 0 < k) (b : Bool) :
    Disjoint (Set.range (c (.initial b))) (Set.range (c .terminal)) := by
  rw [arithmeticLabeledAtlas_terminal_range]
  apply Disjoint.mono_left (arithmeticLabeledAtlas_initial_range_subset hπ data H m k hk b)
  exact arithmeticTensorAtlas_earlier_terminal_disjoint hπ data m k hk
    (Fin.succ ⟨k + 1, by omega⟩) (by dsimp; omega)

/-- The initial/terminal fiber products are empty at every positive retention. -/
theorem arithmeticLabeledAtlas_initial_terminal_isPullback (hpos : 0 < k) (b : Bool) :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) (c (.initial b)) (c .terminal) := by
  let _ := Scheme.isEmpty_pullback (c (.initial b)) (c .terminal)
    (arithmeticLabeledAtlas_initial_terminal_disjoint hπ data H m k hk hpos b)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback (c (.initial b)) (c .terminal))))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

/-- Every earlier retained label misses the entire normalized terminal node. -/
theorem arithmeticLabeledAtlas_earlier_terminal_disjoint (a : Fin k)
    (ha : a.val + 1 < k) (b : Bool) :
    Disjoint (Set.range (c (.retained a b))) (Set.range (c .terminal)) := by
  rw [arithmeticLabeledAtlas_terminal_range]
  apply Disjoint.mono_left (arithmeticLabeledAtlas_retained_range_subset hπ data H m k hk a b)
  exact arithmeticTensorAtlas_earlier_terminal_disjoint hπ data m k hk
    (Fin.succ ⟨k - a.val, by omega⟩) (by dsimp; omega)

/-- The full earlier-label/terminal fiber products are empty, for either label. -/
theorem arithmeticLabeledAtlas_earlier_terminal_isPullback (a : Fin k)
    (ha : a.val + 1 < k) (b : Bool) :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) (c (.retained a b)) (c .terminal) := by
  let _ := Scheme.isEmpty_pullback (c (.retained a b)) (c .terminal)
    (arithmeticLabeledAtlas_earlier_terminal_disjoint hπ data H m k hk a ha b)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback (c (.retained a b)) (c .terminal))))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

end FLT.Mazur.WeierstrassDividedDepth
