/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLabeledAtlas
public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentIndex
public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentAtlas
public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentSeparation

/-!
# Exact adjacent edges in the full labeled arithmetic cover

At every stage, consecutive depths of the same label meet along precisely
the original left/preceding Laurent edge. Different labels have empty
intersection. Both conclusions use the chart maps of the actual open cover.
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
  (a : ℕ) (ha : a + 1 < k)
local notation "Q" => Quotient R π m
local notation "c" => arithmeticLabeledAtlasMap hπ data H m k hk

/-- Every actual same-label consecutive pair meets in the full original polygon atlas edge. -/
theorem arithmeticLabeledAtlas_adjacent_isPullback (b : Bool) :
    IsPullback (PolygonSmoothing.leftBranchOpen Q (parameter R π m))
      (PolygonSmoothing.precedingBranch Q (parameter R π m))
      (c (.retained ⟨a, by omega⟩ b)) (c (.retained ⟨a + 1, ha⟩ b)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (show a + 2 ≤ k by omega)
  dsimp only [arithmeticLabeledAtlasMap, arithmeticLabeledRetainedChart]
  rw [arithmeticRetainedTensorChart_adjacentOld,
    arithmeticRetainedTensorChart_eq hπ data m (a + 2 + r) hk (a + 1) ha r hk]
  exact adjacentArithmeticAtlas_isPullback hπ data m a (by omega) (by omega)
    H.a1_unit (H.scale a) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)
      (H.b3_div _) (H.b4_div _) (H.b6_div _) (H.scale (a + 1)) b r hk

/-- The labeled chart maps satisfy the original adjacent polygon incidence equation. -/
@[reassoc] theorem arithmeticLabeledAtlas_adjacent_overlap (b : Bool) :
    PolygonSmoothing.leftBranchOpen Q (parameter R π m) ≫ c (.retained ⟨a, by omega⟩ b) =
      PolygonSmoothing.precedingBranch Q (parameter R π m) ≫ c (.retained ⟨a + 1, ha⟩ b) :=
  (arithmeticLabeledAtlas_adjacent_isPullback hπ data H m k hk a ha b).w

/-- There are no additional adjacent edges between different labels in the full cover. -/
theorem arithmeticLabeledAtlas_adjacent_crossLabel_isPullback (b d : Bool) (hbd : b ≠ d) :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (c (.retained ⟨a, by omega⟩ b)) (c (.retained ⟨a + 1, ha⟩ d)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (show a + 2 ≤ k by omega)
  dsimp only [arithmeticLabeledAtlasMap, arithmeticLabeledRetainedChart]
  rw [arithmeticRetainedTensorChart_adjacentOld,
    arithmeticRetainedTensorChart_eq hπ data m (a + 2 + r) hk (a + 1) ha r hk]
  exact adjacentArithmeticBranches_crossLabel_isPullback hπ data m a (by omega) (by omega)
    H.a1_unit (H.scale a) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)
      (H.b3_div _) (H.b4_div _) (H.b6_div _) (H.scale (a + 1)) b d hbd r hk

end FLT.Mazur.WeierstrassDividedDepth
