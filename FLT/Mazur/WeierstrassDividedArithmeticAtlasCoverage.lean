/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticAtlasIndex
public import FLT.Mazur.SchemeOpenChartRange

/-!
# Coverage by the original depth-indexed arithmetic tensor charts

Infinity, terminal, initial, and precisely the retained depths exhaust the
original finite cover. This also handles retention zero, with no interior indices.
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
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
  (k : ℕ) (hk : k ≤ n)
local notation "Q" => Quotient R π m

/-- The full terminal chart occupies exactly index one of the arithmetic cover. -/
theorem arithmeticTensorAtlas_terminal_range :
    Set.range (finiteArithmeticDividedTensorChart hπ data m k hk) =
      Set.range (arithmeticTensorAtlasMap hπ data m k hk 1) := by
  rw [← arithmeticTensorAtlas_terminal]
  exact SchemeOpenChartRange.range_iso_comp _ _

/-- The full initial chart occupies exactly the final arithmetic index. -/
theorem arithmeticTensorAtlas_initial_range :
    Set.range (finiteArithmeticInitialTensorChart hπ data m k hk) =
      Set.range (arithmeticTensorAtlasMap hπ data m k hk (Fin.succ ⟨k + 1, by omega⟩)) := by
  rw [← arithmeticTensorAtlas_initial]
  exact SchemeOpenChartRange.range_iso_comp _ _

/-- A retained depth occupies exactly its reverse-depth arithmetic atlas index. -/
theorem arithmeticRetainedTensorChart_range (a : ℕ) (ha : a < k) :
    Set.range (arithmeticRetainedTensorChart hπ data m k hk a ha) =
      Set.range (arithmeticTensorAtlasMap hπ data m k hk (Fin.succ ⟨k - a, by omega⟩)) :=
  SchemeOpenChartRange.range_iso_comp _ _

/-- The explicit original tensor charts cover the whole arithmetic stage at every order. -/
theorem arithmeticDepthTensorCharts_cover (z : finiteGlobalArithmeticStage hπ data k hk m) :
    z ∈ Set.range (arithmeticTensorAtlasMap hπ data m k hk 0) ∨
    z ∈ Set.range (finiteArithmeticDividedTensorChart hπ data m k hk) ∨
    z ∈ Set.range (finiteArithmeticInitialTensorChart hπ data m k hk) ∨
    ∃ (a : ℕ) (ha : a < k), z ∈ Set.range (arithmeticRetainedTensorChart hπ data m k hk a ha) := by
  obtain ⟨i, x, rfl⟩ := arithmeticTensorAtlas_cover hπ data m k hk z
  by_cases h0 : i = 0
  · subst i
    exact Or.inl ⟨x, rfl⟩
  by_cases h1 : i = 1
  · subst i
    exact Or.inr (Or.inl ((arithmeticTensorAtlas_terminal_range hπ data m k hk) ▸ ⟨x, rfl⟩))
  by_cases hi : i = Fin.succ ⟨k + 1, by omega⟩
  · subst i
    exact Or.inr (Or.inr (Or.inl
      ((arithmeticTensorAtlas_initial_range hπ data m k hk) ▸ ⟨x, rfl⟩)))
  have h0' : i.val ≠ 0 := fun h => h0 (Fin.ext h)
  have h1' : i.val ≠ 1 := fun h => h1 (Fin.ext h)
  have hi' : i.val ≠ k + 2 := fun h => hi (Fin.ext h)
  have ha : k + 1 - i.val < k := by omega
  refine Or.inr (Or.inr (Or.inr ⟨k + 1 - i.val, ha, ?_⟩))
  rw [arithmeticRetainedTensorChart_range]
  have he : (Fin.succ ⟨k - (k + 1 - i.val), by omega⟩ : Fin (k + 3)) = i := by
    ext
    dsimp
    omega
  rw [he]
  exact ⟨x, rfl⟩

end FLT.Mazur.WeierstrassDividedDepth
