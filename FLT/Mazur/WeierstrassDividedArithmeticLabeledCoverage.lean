/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLabeledCharts

/-!
# Full coverage by the constructed labeled arithmetic charts

The normalized terminal node retains the entire terminal chart. Both full
initial nodes and both labels at each retained depth cover their original
charts, so together with the unchanged infinity chart they cover the stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (k : ℕ) (hk : k ≤ n)
local notation "Q" => Quotient R π m
local notation "d₀" => data (Fin.mk 0 (Nat.zero_lt_succ n))

/-- The two labeled full initial nodes cover exactly the whole original initial chart. -/
theorem arithmeticLabeledInitialChart_image :
    Set.range (arithmeticLabeledInitialChart hπ data H m k hk false) ∪
      Set.range (arithmeticLabeledInitialChart hπ data H m k hk true) =
        Set.range (finiteArithmeticInitialTensorChart hπ data m k hk) := by
  apply Set.Subset.antisymm
  · rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ | ⟨y, hy⟩ := arithmeticInitialTensorNodeCharts_cover π m W
      (π ^ start) (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) H.a1_unit H.a2_div
        (H.b3_div _) (H.b4_div _) (H.b6_div _) x
    · exact Or.inl ⟨y, congrArg (finiteArithmeticInitialTensorChart hπ data m k hk) hy⟩
    · exact Or.inr ⟨y, congrArg (finiteArithmeticInitialTensorChart hπ data m k hk) hy⟩

/-- Both retained labels cover the full original tensor chart at precisely that depth. -/
theorem arithmeticLabeledRetainedChart_image (a : Fin k) :
    Set.range (arithmeticLabeledRetainedChart hπ data H m k hk a false) ∪
      Set.range (arithmeticLabeledRetainedChart hπ data H m k hk a true) =
        Set.range (arithmeticRetainedTensorChart hπ data m k hk a.val a.isLt) :=
  arithmeticTensorBranches_image π m W (π ^ (start + a.val))
    (data ⟨a.val + 1, by omega⟩).b3 (data ⟨a.val + 1, by omega⟩).b4
    (data ⟨a.val + 1, by omega⟩).b6 H.a1_unit (H.scale a.val) H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _) _

/-- Terminal normalization keeps the entire terminal image, including its horizontal origin. -/
theorem arithmeticLabeledTerminalChart_image :
    Set.range (arithmeticLabeledTerminalChart hπ data H m k hk) =
      Set.range (finiteArithmeticDividedTensorChart hπ data m k hk) :=
  SchemeOpenChartRange.range_iso_comp _ _

/-- The full labeled charts and the unchanged original infinity chart cover every stage point. -/
theorem arithmeticLabeledCharts_cover (z : finiteGlobalArithmeticStage hπ data k hk m) :
    z ∈ Set.range (arithmeticTensorAtlasMap hπ data m k hk 0) ∨
    z ∈ Set.range (arithmeticLabeledTerminalChart hπ data H m k hk) ∨
    (∃ label, z ∈ Set.range (arithmeticLabeledInitialChart hπ data H m k hk label)) ∨
    ∃ (a : Fin k), ∃ label,
      z ∈ Set.range (arithmeticLabeledRetainedChart hπ data H m k hk a label) := by
  obtain h | h | h | ⟨a, ha, h⟩ := arithmeticDepthTensorCharts_cover hπ data m k hk z
  · exact Or.inl h
  · exact Or.inr (Or.inl ((arithmeticLabeledTerminalChart_image hπ data H m k hk) ▸ h))
  · rw [← arithmeticLabeledInitialChart_image hπ data H m k hk] at h
    rcases h with h | h
    · exact Or.inr (Or.inr (Or.inl ⟨false, h⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨true, h⟩))
  · have h' : z ∈ Set.range (arithmeticRetainedTensorChart hπ data m k hk a ha) := h
    rw [← arithmeticLabeledRetainedChart_image hπ data H m k hk ⟨a, ha⟩] at h'
    rcases h' with h' | h'
    · exact Or.inr (Or.inr (Or.inr ⟨⟨a, ha⟩, false, h'⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨⟨a, ha⟩, true, h'⟩))

end FLT.Mazur.WeierstrassDividedDepth
