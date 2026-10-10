/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalTensorEmbedding

/-!
# The original tensor infinity chart covers the global base change

The unchanged projective Y-chart gives an actual tensor-algebra chart.
Together with the entire finite local tensor model it covers every point
of the whole projective coefficient pullback.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (j : ℕ) (hj : j ≤ n)
open WeierstrassIntegralChart
open scoped TensorProduct
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- The original infinity tensor algebra embeds into the global coefficient pullback. -/
def finiteInfinityTensorChart :
    Spec (.of (S ⊗[R] Coordinate W 1)) ⟶ finiteGlobalTensorModel hπ data S j hj :=
  TensorOpenChart.chart _ _ (finiteInfinityChart_structure hπ data j hj)

instance finiteInfinityTensorChart_isOpenImmersion :
    IsOpenImmersion (finiteInfinityTensorChart hπ data S j hj) :=
  inferInstanceAs (IsOpenImmersion (TensorOpenChart.chart _ _ _))

/-- Infinity retains the full original integral chart under base change. -/
theorem finiteInfinityTensorChart_isPullback :
    IsPullback (finiteInfinityTensorChart hπ data S j hj) TensorOpenChart.projection
      (pullback.snd q (finiteGlobalStructure hπ data j hj))
        (finiteInfinityChart hπ data j hj) :=
  TensorOpenChart.chart_isPullback _ _ _

/-- The tensor infinity chart covers the full inverse image of the original infinity chart. -/
theorem finiteInfinityTensorChart_range :
    Set.range (finiteInfinityTensorChart hπ data S j hj) =
      (pullback.snd q (finiteGlobalStructure hπ data j hj)) ⁻¹'
        Set.range (finiteInfinityChart hπ data j hj) :=
  TensorOpenChart.chart_range _ _ _

/-- The entire infinity tensor algebra retains its extended coefficient structure. -/
@[reassoc] theorem finiteInfinityTensorChart_structure :
    finiteInfinityTensorChart hπ data S j hj ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] Coordinate W 1))) :=
  TensorOpenChart.chart_fst _ _ _

/-- All original infinity-chart functions retain their projective cubic contraction. -/
@[reassoc] theorem finiteInfinityTensorChart_toCurve :
    finiteInfinityTensorChart hπ data S j hj ≫
      pullback.snd q (finiteGlobalStructure hπ data j hj) ≫
        finiteGlobalContraction hπ data j hj =
      TensorOpenChart.projection ≫ integralCurveChart W 1 := by
  rw [← Category.assoc]
  change (TensorOpenChart.chart _ _ _ ≫ _) ≫ _ = _
  rw [TensorOpenChart.chart_snd, Category.assoc, finiteInfinityChart_contraction]

/-- Infinity and the entire finite local tensor model cover the whole global pullback. -/
theorem finiteGlobalTensor_charts_cover (z : finiteGlobalTensorModel hπ data S j hj) :
    (∃ a, finiteInfinityTensorChart hπ data S j hj a = z) ∨
      ∃ a, finiteLocalTensorEmbedding hπ data S j hj a = z := by
  change z ∈ Set.range (finiteInfinityTensorChart hπ data S j hj) ∪
    Set.range (finiteLocalTensorEmbedding hπ data S j hj)
  rw [finiteInfinityTensorChart_range, finiteLocalTensorEmbedding_range]
  exact finiteGlobal_charts_cover hπ data j hj (pullback.snd q _ z)

end FLT.Mazur.WeierstrassDividedDepth
