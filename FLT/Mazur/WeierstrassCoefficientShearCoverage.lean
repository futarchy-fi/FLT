/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedCoefficientShearChart
public import FLT.Mazur.WeierstrassDividedCoefficientShearGlobalCharts

/-!
# Coverage by the full sheared coefficient equations

The original infinity chart, sheared divided and incidence equations, and
all retained sheared successive equations cover at every depth, including zero.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S) (t : ℕ) (ht : t ≤ n)

/-- The whole sheared divided equation occupies global atlas index one. -/
theorem globalDividedCoefficientShearChart_range_index :
    Set.range (globalDividedCoefficientShearChart hπ data S r t ht) =
      Set.range (globalTensorAtlasMap hπ data S t ht 1) := by
  rw [globalDividedCoefficientShearChart_range]
  have h : (finiteDividedTensorAtlasIso hπ data S t ht).hom ≫
      globalTensorAtlasMap hπ data S t ht 1 = globalDividedTensorChart hπ data S t ht := by
    change _ ≫ (finiteTensorAtlasMap hπ data S t ht 0 ≫ _) = _
    rw [finiteDividedTensorAtlasIso_map_assoc]
    rfl
  rw [← h]
  exact SchemeOpenChartRange.range_iso_comp (finiteDividedTensorAtlasIso hπ data S t ht) _

/-- The whole sheared incidence equation occupies the final global atlas index. -/
theorem globalInitialCoefficientShearChart_range_index :
    Set.range (globalInitialCoefficientShearChart hπ data S r t ht) =
      Set.range (globalTensorAtlasMap hπ data S t ht ⟨t + 2, by omega⟩) := by
  rw [globalInitialCoefficientShearChart_range, ← globalInitialTensorChart_eq_index]
  exact SchemeOpenChartRange.range_iso_comp (finiteInitialTensorAtlasIso hπ data S t ht) _

/-- Every point lies in one of the full coefficient/shear equations or original infinity. -/
theorem coefficientShearCharts_cover (z : finiteGlobalTensorModel hπ data S t ht) :
    z ∈ Set.range (finiteInfinityTensorChart hπ data S t ht) ∨
    z ∈ Set.range (globalDividedCoefficientShearChart hπ data S r t ht) ∨
    z ∈ Set.range (globalInitialCoefficientShearChart hπ data S r t ht) ∨
    ∃ j : Fin t, z ∈ Set.range
      (retainedCoefficientShearChart hπ data S r t ht j.val (by omega)) := by
  obtain ⟨i, x, hx⟩ := globalTensorAtlas_cover hπ data S t ht z
  have hz : z ∈ Set.range (globalTensorAtlasMap hπ data S t ht i) := ⟨x, hx⟩
  by_cases h0 : i.val = 0
  · left
    have hi : i = 0 := Fin.ext h0
    subst i
    exact hz
  by_cases h1 : i.val = 1
  · right; left
    rw [globalDividedCoefficientShearChart_range_index]
    have hi : i = 1 := Fin.ext h1
    subst i
    exact hz
  by_cases hlast : i.val = t + 2
  · right; right; left
    rw [globalInitialCoefficientShearChart_range_index]
    have hi : i = ⟨t + 2, by omega⟩ := Fin.ext hlast
    exact (congrArg (fun k => z ∈ Set.range
      (globalTensorAtlasMap hπ data S t ht k)) hi).mp hz
  · right; right; right
    refine ⟨⟨t + 1 - i.val, by omega⟩, ?_⟩
    rw [retainedCoefficientShearChart_range_index]
    have hi : (⟨t - (t + 1 - i.val) + 1, by omega⟩ : Fin (t + 3)) = i :=
      Fin.ext (by dsimp; omega)
    exact (congrArg (fun k => z ∈ Set.range
      (globalTensorAtlasMap hπ data S t ht k)) hi).mpr hz

end FLT.Mazur.WeierstrassDividedDepth
