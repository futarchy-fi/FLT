/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTensorYBoundary

/-!
# Full overlap and gluing of the global tensor model

The entire tensor algebra of the original Y-boundary is the cartesian
intersection of infinity and the finite local tensor model. Their open
pushout is the actual projective coefficient pullback.
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
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "b" => finiteTensorYBoundary hπ data S j hj
local notation "e" => tensorBoundaryToInfinity (W := W) S
local notation "l" => finiteInfinityTensorChart hπ data S j hj
local notation "r" => finiteLocalTensorEmbedding hπ data S j hj

/-- The whole original tensor overlap commutes inside the global model. -/
@[reassoc] theorem finiteGlobalTensor_overlap : e ≫ l = b ≫ r := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, finiteInfinityTensorChart_structure,
      finiteLocalTensorEmbedding_structure, tensorBoundaryToInfinity_structure]
    exact (TensorOpenChart.chart_fst _ _ _).symm
  · rw [Category.assoc, Category.assoc, finiteLocalTensorEmbedding_square]
    change e ≫ (TensorOpenChart.chart _ _ _ ≫ _) =
      (TensorOpenChart.chart _ _ _) ≫ _ ≫ _
    rw [TensorOpenChart.chart_snd, tensorBoundaryToInfinity_projection_assoc,
      TensorOpenChart.chart_snd_assoc]
    change TensorOpenChart.projection ≫ affineBoundaryToY W ≫ pushout.inl _ _ =
      TensorOpenChart.projection ≫ finiteYBoundary hπ data j hj ≫ pushout.inr _ _
    rw [pushout.condition]

/-- No points outside the original full overlap identify the two tensor charts. -/
theorem finiteGlobalTensor_overlap_preimage : r ⁻¹' Set.range l = Set.range b := by
  rw [finiteInfinityTensorChart_range]
  change r ⁻¹' (pullback.snd q (finiteGlobalStructure hπ data j hj)) ⁻¹'
    Set.range (finiteInfinityChart hπ data j hj) = _
  rw [show Set.range b = (pullback.snd q (finiteStructure hπ data j hj)) ⁻¹'
    Set.range (finiteYBoundary hπ data j hj) from TensorOpenChart.chart_range _ _ _]
  ext z
  change pullback.snd q (finiteGlobalStructure hπ data j hj) (r z) ∈
    Set.range (finiteInfinityChart hπ data j hj) ↔ _
  have hz : pullback.snd q (finiteGlobalStructure hπ data j hj) (r z) =
      finiteLocalChart hπ data j hj (pullback.snd q (finiteStructure hπ data j hj) z) :=
    congrArg (fun f => f z) (finiteLocalTensorEmbedding_square hπ data S j hj)
  rw [hz]
  exact Set.ext_iff.mp (SchemeOpenPushout.inr_preimage_inl
    (affineBoundaryToY W) (finiteYBoundary hπ data j hj)) _

/-- The whole boundary tensor algebra is the actual cartesian intersection of the two charts. -/
theorem finiteGlobalTensor_overlap_isPullback : IsPullback e b l r := by
  apply IsOpenImmersion.isPullback e b l r (finiteGlobalTensor_overlap hπ data S j hj).symm
  exact TopologicalSpace.Opens.ext (finiteGlobalTensor_overlap_preimage hπ data S j hj)

/-- Gluing the full original tensor boundary recovers the actual global coefficient pullback. -/
def finiteGlobalTensorGluingIso :
    pushout e b ≅ finiteGlobalTensorModel hπ data S j hj :=
  SchemeOpenPushout.coverIso e b l r (finiteGlobalTensor_overlap_isPullback hπ data S j hj)
    (finiteGlobalTensor_charts_cover hπ data S j hj)

/-- The gluing comparison retains the actual infinity tensor inclusion. -/
@[reassoc] theorem finiteGlobalTensorGluingIso_infinity :
    pushout.inl e b ≫ (finiteGlobalTensorGluingIso hπ data S j hj).hom = l :=
  SchemeOpenPushout.inl_coverIso _ _ _ _ _ _

/-- The gluing comparison retains the entire finite local tensor model. -/
@[reassoc] theorem finiteGlobalTensorGluingIso_local :
    pushout.inr e b ≫ (finiteGlobalTensorGluingIso hπ data S j hj).hom = r :=
  SchemeOpenPushout.inr_coverIso _ _ _ _ _ _

end FLT.Mazur.WeierstrassDividedDepth
