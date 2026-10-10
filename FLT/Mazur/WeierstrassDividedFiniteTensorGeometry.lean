/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteTensorCharts

/-!
# Retained images and contractions of the finite tensor atlas

The tensor charts cover the full inverse images of the integral atlas
charts and keep the original cubic contraction on all their functions.
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
  (S : Type u) [CommRing S] [Algebra R S]
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- The terminal tensor chart covers precisely the full integral divided-chart preimage. -/
theorem finiteDividedTensorChart_range (j : ℕ) (hj : j ≤ n) :
    Set.range (finiteDividedTensorChart hπ data S j hj) =
      (pullback.snd q (finiteStructure hπ data j hj)) ⁻¹'
        Set.range (finiteExterior hπ data E₀ j hj).dividedChart :=
  TensorOpenChart.chart_range _ _ _

/-- The successive tensor chart covers precisely its original atlas-chart preimage. -/
theorem finiteSuccessiveTensorChart_range (j : ℕ) (hj : j + 1 ≤ n) :
    Set.range (finiteSuccessiveTensorChart hπ data S j hj) =
      (pullback.snd q (finiteStructure hπ data (j + 1) hj)) ⁻¹'
        Set.range (finiteAtlasMap hπ data E₀ (j + 1) hj 1) :=
  TensorOpenChart.chart_range _ _ _

/-- The terminal tensor chart retains its full original-cubic contraction. -/
@[reassoc] theorem finiteDividedTensorChart_toCurve (j : ℕ) (hj : j ≤ n) :
    finiteDividedTensorChart hπ data S j hj ≫
      pullback.snd q (finiteStructure hπ data j hj) ≫ finiteToCurve hπ data j hj =
        TensorOpenChart.projection ≫ toCurve (data ⟨j, Nat.lt_succ_of_le hj⟩) := by
  rw [← Category.assoc]
  change (TensorOpenChart.chart _ _ _ ≫ _) ≫ _ = _
  rw [TensorOpenChart.chart_snd, Category.assoc, finiteDivided_toCurve]

/-- The newest tensor chart retains the actual successive coordinate contraction. -/
@[reassoc] theorem finiteSuccessiveTensorChart_toCurve (j : ℕ) (hj : j + 1 ≤ n) :
    finiteSuccessiveTensorChart hπ data S j hj ≫
      pullback.snd q (finiteStructure hπ data (j + 1) hj) ≫
        finiteToCurve hπ data (j + 1) hj =
      TensorOpenChart.projection ≫
        xContraction hπ (data ⟨j, Nat.lt_succ_of_le (Nat.le_of_succ_le hj)⟩)
          (data ⟨j + 1, Nat.lt_succ_of_le hj⟩) ≫
            toCurve (data ⟨j, Nat.lt_succ_of_le (Nat.le_of_succ_le hj)⟩) := by
  rw [← Category.assoc]
  change (TensorOpenChart.chart _ _ _ ≫ _) ≫ _ = _
  rw [TensorOpenChart.chart_snd, Category.assoc]
  change TensorOpenChart.projection ≫
    (finiteExteriorAtlasMap hπ data E₀ (j + 1) hj 0 ≫
      (finiteExterior hπ data E₀ (j + 1) hj).exteriorChart) ≫ _ = _
  rw [Category.assoc, finiteExteriorAtlas_new_toCurve]

/-- The terminal chart retains the new coefficient structure. -/
@[reassoc] theorem finiteDividedTensorChart_structure (j : ℕ) (hj : j ≤ n) :
    finiteDividedTensorChart hπ data S j hj ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S
        (WeierstrassDilatation.ScalarExtension W (π ^ (start + j))
          (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j, Nat.lt_succ_of_le hj⟩).b4
          (data ⟨j, Nat.lt_succ_of_le hj⟩).b6 S))) :=
  TensorOpenChart.chart_fst _ _ _

/-- The successive chart retains the same new coefficient structure. -/
@[reassoc] theorem finiteSuccessiveTensorChart_structure (j : ℕ) (hj : j + 1 ≤ n) :
    finiteSuccessiveTensorChart hπ data S j hj ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S
        (WeierstrassSuccessiveX.ScalarExtension W (π ^ (start + j)) π
          (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3
          (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4
          (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 S))) :=
  TensorOpenChart.chart_fst _ _ _

end FLT.Mazur.WeierstrassDividedDepth
