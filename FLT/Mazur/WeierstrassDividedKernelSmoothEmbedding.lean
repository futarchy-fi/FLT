/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedKernelContraction

/-!
# The original smooth kernel inside its full divided closure

The exact original smooth intersection embeds into the newly constructed full
closure. Dense generic equations construct this map; its ambient inclusion,
contraction, structure map and original generic source are all retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false

variable {R K : Type} [CommRing R] [IsDomain R] [IsBezout R]
  [Field K] [Algebra R K]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (hΔ : IsUnit (W.map (algebraMap R K)).Δ)
  {H : Scheme} (i : H ⟶ integralCurve (W.map (algebraMap R K))) [IsClosedImmersion i]

/-- Retain the original smooth kernel in the full divided closure by its dense equations. -/
def finiteGlobalKernelSmoothEmbedding :
    genericClosureSmoothPart W i ⟶ finiteGlobalKernelClosure hπ data j hj hΔ i :=
  DenseClosedRestriction.lift (genericKernelToClosureSmooth W hΔ i)
    (finiteGlobalKernelClosureInclusion hπ data j hj hΔ i)
    (genericClosureSmoothInclusion W i ≫ finiteGlobalSmoothEmbedding hπ data j hj)
    (finiteGlobalKernelToClosure hπ data j hj hΔ i) (by
      rw [genericKernelToClosureSmooth_inclusion_assoc, finiteGlobalKernelToClosure_inclusion]
      rfl)

/-- Its ambient embedding is the existing original smooth kernel inclusion. -/
@[reassoc] theorem finiteGlobalKernelSmoothEmbedding_inclusion :
    finiteGlobalKernelSmoothEmbedding hπ data j hj hΔ i ≫
      finiteGlobalKernelClosureInclusion hπ data j hj hΔ i =
        genericClosureSmoothInclusion W i ≫ finiteGlobalSmoothEmbedding hπ data j hj :=
  DenseClosedRestriction.lift_inclusion _ _ _ _ _

/-- The full original generic kernel is retained through the smooth embedding. -/
@[reassoc] theorem genericKernelToClosureSmooth_dividedEmbedding :
    genericKernelToClosureSmooth W hΔ i ≫ finiteGlobalKernelSmoothEmbedding hπ data j hj hΔ i =
      finiteGlobalKernelToClosure hπ data j hj hΔ i :=
  DenseClosedRestriction.dense_lift _ _ _ _ _

/-- Contraction on this open kernel is its precise original map into the full closure. -/
@[reassoc] theorem finiteGlobalKernelSmoothEmbedding_contraction :
    finiteGlobalKernelSmoothEmbedding hπ data j hj hΔ i ≫
      finiteGlobalKernelClosureContraction hπ data j hj hΔ i =
        genericClosureSmoothToClosure W i := by
  apply (cancel_mono (genericKernelClosureInclusion W i)).mp
  rw [Category.assoc, finiteGlobalKernelClosureContraction_inclusion,
    finiteGlobalKernelSmoothEmbedding_inclusion_assoc,
    finiteGlobalSmoothEmbedding_contraction]
  exact (genericClosureSmooth_isPullback W i).w.symm

/-- The original integral coefficient structure is unchanged. -/
@[reassoc] theorem finiteGlobalKernelSmoothEmbedding_structure :
    finiteGlobalKernelSmoothEmbedding hπ data j hj hΔ i ≫
      finiteGlobalKernelClosureStructure hπ data j hj hΔ i = genericClosureSmoothStructure W i := by
  rw [← finiteGlobalKernelClosureContraction_structure,
    finiteGlobalKernelSmoothEmbedding_contraction_assoc]
  rfl

/-- The comparison with the actual inverse image of the original smooth ambient scheme. -/
def finiteGlobalKernelSmoothComparison : genericClosureSmoothPart W i ⟶
    pullback (finiteGlobalKernelClosureInclusion hπ data j hj hΔ i)
      (finiteGlobalSmoothEmbedding hπ data j hj) :=
  pullback.lift (finiteGlobalKernelSmoothEmbedding hπ data j hj hΔ i)
    (genericClosureSmoothInclusion W i)
    (finiteGlobalKernelSmoothEmbedding_inclusion hπ data j hj hΔ i)

/-- The comparison keeps the actual embedding into the divided closure. -/
@[reassoc] theorem finiteGlobalKernelSmoothComparison_fst :
    finiteGlobalKernelSmoothComparison hπ data j hj hΔ i ≫ pullback.fst _ _ =
      finiteGlobalKernelSmoothEmbedding hπ data j hj hΔ i := pullback.lift_fst _ _ _

/-- The comparison keeps the exact original smooth ambient inclusion. -/
@[reassoc] theorem finiteGlobalKernelSmoothComparison_snd :
    finiteGlobalKernelSmoothComparison hπ data j hj hΔ i ≫ pullback.snd _ _ =
      genericClosureSmoothInclusion W i := pullback.lift_snd _ _ _

end FLT.Mazur.WeierstrassDividedDepth
