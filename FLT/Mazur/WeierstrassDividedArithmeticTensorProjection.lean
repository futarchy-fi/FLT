/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticAtlasIndex

/-!
# Original integral projections of every arithmetic tensor chart

The initial, divided and all older successive tensor charts project to their
original integral charts at the specified fixed stage. Infinity keeps its
original projective chart as well.
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
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))

/-- The full initial tensor chart retains its integral chart at every fixed stage. -/
@[reassoc] theorem finiteArithmeticInitialTensorChart_projection (k : ℕ) (hk : k ≤ n) :
    finiteArithmeticInitialTensorChart hπ data m k hk ≫
      finiteGlobalArithmeticProjection hπ data k hk m =
        TensorOpenChart.projection ≫ finiteInitialChart hπ data k hk ≫
          finiteLocalChart hπ data k hk := by
  change (globalInitialTensorChart hπ data Q k hk ≫
    (pullbackSymmetry q (finiteGlobalStructure hπ data k hk)).hom) ≫
      pullback.fst _ _ = _
  rw [Category.assoc, pullbackSymmetry_hom_comp_fst, globalInitialTensorChart,
    Category.assoc, finiteLocalTensorEmbedding_square]
  change TensorOpenChart.chart _ _ _ ≫ _ ≫ _ = _
  rw [TensorOpenChart.chart_snd_assoc]

/-- The full divided chart projects to the original terminal integral chart. -/
@[reassoc] theorem finiteArithmeticDividedTensorChart_projection (k : ℕ) (hk : k ≤ n) :
    finiteArithmeticDividedTensorChart hπ data m k hk ≫
      finiteGlobalArithmeticProjection hπ data k hk m =
        TensorOpenChart.projection ≫ (finiteExterior hπ data E₀ k hk).dividedChart ≫
          finiteLocalChart hπ data k hk := by
  change (globalDividedTensorChart hπ data Q k hk ≫
    (pullbackSymmetry q (finiteGlobalStructure hπ data k hk)).hom) ≫
      pullback.fst _ _ = _
  rw [Category.assoc, pullbackSymmetry_hom_comp_fst, globalDividedTensorChart,
    Category.assoc, finiteLocalTensorEmbedding_square]
  change TensorOpenChart.chart _ _ _ ≫ _ ≫ _ = _
  rw [TensorOpenChart.chart_snd_assoc]

/-- Arbitrary retention leaves the original integral chart projection intact. -/
@[reassoc] theorem finiteArithmeticOlderTensorChart_projection
    (a : ℕ) (ha : a + 1 ≤ n) (r : ℕ) (hr : a + 1 + r ≤ n) :
    finiteArithmeticOlderTensorChart hπ data m a ha r hr ≫
      finiteGlobalArithmeticProjection hπ data (a + 1 + r) hr m =
        TensorOpenChart.projection ≫ olderSuccessiveChart hπ data a ha r hr ≫
          finiteLocalChart hπ data (a + 1 + r) hr := by
  change (olderGlobalTensorChart hπ data Q a ha r hr ≫
    (pullbackSymmetry q (finiteGlobalStructure hπ data (a + 1 + r) hr)).hom) ≫
      pullback.fst _ _ = _
  rw [Category.assoc, pullbackSymmetry_hom_comp_fst, olderGlobalTensorChart,
    Category.assoc, finiteLocalTensorEmbedding_square]
  change TensorOpenChart.chart _ _ _ ≫ _ ≫ _ = _
  rw [TensorOpenChart.chart_snd_assoc]

/-- The indexed infinity tensor chart retains its original projective chart. -/
@[reassoc] theorem arithmeticTensorAtlas_infinity_projection (k : ℕ) (hk : k ≤ n) :
    arithmeticTensorAtlasMap hπ data m k hk 0 ≫
      finiteGlobalArithmeticProjection hπ data k hk m =
        TensorOpenChart.projection ≫ finiteInfinityChart hπ data k hk := by
  change (finiteInfinityTensorChart hπ data Q k hk ≫
    (pullbackSymmetry q (finiteGlobalStructure hπ data k hk)).hom) ≫
      pullback.fst _ _ = _
  rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
  exact TensorOpenChart.chart_snd _ _ _

/-- Infinity also retains the exact quotient coefficient structure. -/
@[reassoc] theorem arithmeticTensorAtlas_infinity_structure (k : ℕ) (hk : k ≤ n) :
    arithmeticTensorAtlasMap hπ data m k hk 0 ≫
      finiteGlobalArithmeticStructure hπ data k hk m =
        Spec.map (CommRingCat.ofHom (algebraMap Q
          (TensorProduct R Q (WeierstrassIntegralChart.Coordinate W 1)))) := by
  change (finiteInfinityTensorChart hπ data Q k hk ≫
    (pullbackSymmetry q (finiteGlobalStructure hπ data k hk)).hom) ≫
      pullback.snd _ _ = _
  rw [Category.assoc, pullbackSymmetry_hom_comp_snd, finiteInfinityTensorChart_structure]

end FLT.Mazur.WeierstrassDividedDepth
