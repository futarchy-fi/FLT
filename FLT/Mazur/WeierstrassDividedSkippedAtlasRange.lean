/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSkippedTensorIntersection

/-!
# Every earlier indexed chart lies in the skipped exterior

Unrolling the actual finite atlas retains all earlier chart maps, including
the initial exterior, inside the exterior before the intervening chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "fData" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "E" => finiteExterior hπ data E₀ j (Nat.le_of_succ_le hj)
local notation "F" => Exterior.advance hπ (E) e
local notation "tail" => finiteStageRetained hπ data (j + 2) hjNext r hr ≫
  Exterior.exteriorChart (finiteExterior hπ data E₀ (j + 2 + r) hr)
local notation "base" => finiteStructure hπ data (j + 2 + r) hr
local notation "new" => olderSuccessiveChart hπ data (j + 1) hjNext r hr

/-- Every older indexed exterior chart factors pointwise through the full skipped exterior. -/
theorem skippedExteriorAtlas_range_subset (i : Fin (j + 1)) :
    Set.range (finiteExteriorAtlasMap hπ data E₀ (j + 2 + r) hr
      ⟨i.val + 2 + r, by omega⟩) ⊆
        Set.range ((E).retained hπ e ≫ (F).retained hπ fData ≫
          finiteStageRetained hπ data (j + 2) hjNext r hr) := by
  induction r with
  | zero =>
    rintro _ ⟨a, rfl⟩
    refine ⟨finiteExteriorAtlasMap hπ data E₀ j (Nat.le_of_succ_le hj) i a, ?_⟩
    rfl
  | succ r ih =>
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := ih (Nat.le_of_succ_le hr)
      ⟨a, rfl⟩
    refine ⟨b, ?_⟩
    change ((finiteExterior hπ data E₀ (j + 2 + r) (Nat.le_of_succ_le hr)).retained
      hπ _) (((E).retained hπ e ≫ (F).retained hπ fData ≫
        finiteStageRetained hπ data (j + 2) hjNext r (Nat.le_of_succ_le hr)) b) = _
    rw [hb]
    rfl

/-- The actual retained full-atlas indices all lie in the original skipped exterior. -/
theorem skippedFiniteAtlas_range_subset (i : Fin (j + 1)) :
    Set.range (finiteAtlasMap hπ data E₀ (j + 2 + r) hr
      ⟨i.val + 2 + r + 1, by omega⟩) ⊆
        Set.range (skippedExteriorChart hπ data j hj hjNext r hr) := by
  rintro _ ⟨a, rfl⟩
  obtain ⟨b, hb⟩ := skippedExteriorAtlas_range_subset hπ data j hj hjNext r hr i ⟨a, rfl⟩
  refine ⟨b, ?_⟩
  exact congrArg (Exterior.exteriorChart
    (finiteExterior hπ data E₀ (j + 2 + r) hr)) hb

end FLT.Mazur.WeierstrassDividedDepth
