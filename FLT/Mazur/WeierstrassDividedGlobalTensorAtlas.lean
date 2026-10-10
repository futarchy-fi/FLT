/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteTensorAtlas
public import FLT.Mazur.WeierstrassDividedGlobalTensorInfinity

/-!
# The complete finite open atlas of the global coefficient pullback

The infinity tensor chart and every indexed local chart form an actual
finite open cover. It includes the initial exterior at k=0, all retained
successive charts, and the terminal divided chart.
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
open scoped TensorProduct
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- Infinity followed by the full indexed local coefficient pullbacks. -/
def globalTensorAtlasObject : Fin (j + 3) → Scheme :=
  Fin.cases (Spec (.of (S ⊗[R] WeierstrassIntegralChart.Coordinate W 1)))
    (finiteTensorAtlasObject hπ data S j hj)

/-- Every chart of the full finite tensor atlas embeds in the projective coefficient pullback. -/
def globalTensorAtlasMap (i : Fin (j + 3)) :
    globalTensorAtlasObject hπ data S j hj i ⟶ finiteGlobalTensorModel hπ data S j hj :=
  Fin.cases (finiteInfinityTensorChart hπ data S j hj)
    (fun a => finiteTensorAtlasMap hπ data S j hj a ≫
      finiteLocalTensorEmbedding hπ data S j hj) i

instance globalTensorAtlasMap_isOpenImmersion (i : Fin (j + 3)) :
    IsOpenImmersion (globalTensorAtlasMap hπ data S j hj i) := by
  cases i using Fin.cases with
  | zero => change IsOpenImmersion (finiteInfinityTensorChart hπ data S j hj); infer_instance
  | succ i =>
    change IsOpenImmersion (_ ≫ finiteLocalTensorEmbedding hπ data S j hj)
    infer_instance

/-- The full indexed atlas covers every point of the global coefficient pullback. -/
theorem globalTensorAtlas_cover (z : finiteGlobalTensorModel hπ data S j hj) :
    ∃ i x, globalTensorAtlasMap hπ data S j hj i x = z := by
  rcases finiteGlobalTensor_charts_cover hπ data S j hj z with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact ⟨0, x, rfl⟩
  · obtain ⟨i, y, rfl⟩ := finiteTensorAtlas_cover hπ data S j hj x
    exact ⟨i.succ, y, rfl⟩

/-- Package the complete actual finite global atlas as an open cover. -/
def globalTensorOpenCover : (finiteGlobalTensorModel hπ data S j hj).OpenCover where
  I₀ := Fin (j + 3)
  X := globalTensorAtlasObject hπ data S j hj
  f := globalTensorAtlasMap hπ data S j hj
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨globalTensorAtlas_cover hπ data S j hj,
      fun i => globalTensorAtlasMap_isOpenImmersion hπ data S j hj i⟩

/-- Every indexed local chart retains its original cubic contraction in the global atlas. -/
@[reassoc] theorem globalTensorAtlasMap_local_toCurve (i : Fin (j + 2)) :
    globalTensorAtlasMap hπ data S j hj i.succ ≫
      pullback.snd q (finiteGlobalStructure hπ data j hj) ≫
        finiteGlobalContraction hπ data j hj =
      finiteTensorAtlasMap hπ data S j hj i ≫
        pullback.snd q (finiteStructure hπ data j hj) ≫ finiteToCurve hπ data j hj := by
  change (_ ≫ finiteLocalTensorEmbedding hπ data S j hj) ≫ _ ≫ _ = _
  rw [Category.assoc, finiteLocalTensorEmbedding_toCurve]

end FLT.Mazur.WeierstrassDividedDepth
