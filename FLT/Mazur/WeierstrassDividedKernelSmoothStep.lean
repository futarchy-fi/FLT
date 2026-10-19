/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedKernelSmoothRecovery
public import FLT.Mazur.WeierstrassDividedKernelStep

/-!
# The unchanged original smooth kernel through the full closure comparisons

Contraction changes nothing over the original smooth kernel, and each successor
restriction preserves its exact open embedding. These are statements about the
constructed full closures and their concrete maps, without replacing their carriers.
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

/-- The full closure contraction is unchanged over the entire original smooth kernel. -/
theorem finiteGlobalKernelClosureContraction_smooth_isPullback :
    IsPullback (𝟙 _) (finiteGlobalKernelSmoothEmbedding hπ data j hj hΔ i)
      (genericClosureSmoothToClosure W i)
      (finiteGlobalKernelClosureContraction hπ data j hj hΔ i) := by
  have h := (finiteGlobalKernelSmoothEmbedding_isPullback hπ data j hj hΔ i).paste_vert
    (finiteGlobalSmoothEmbedding_isPullback hπ data j hj).flip
  have hbig : IsPullback (𝟙 _ ≫ genericClosureSmoothInclusion W i)
      (finiteGlobalKernelSmoothEmbedding hπ data j hj hΔ i) (integralSmoothOpen W).ι
      (finiteGlobalKernelClosureContraction hπ data j hj hΔ i ≫
        genericKernelClosureInclusion W i) := by
    simpa only [Category.comp_id, Category.id_comp,
      finiteGlobalKernelClosureContraction_inclusion] using h.flip
  exact hbig.of_right (by
    rw [Category.id_comp, finiteGlobalKernelSmoothEmbedding_contraction])
    (genericClosureSmooth_isPullback W i).flip

/-- Every concrete full-kernel step keeps the same original smooth open embedding. -/
@[reassoc] theorem finiteGlobalKernelSmoothEmbedding_step (hnext : j + 1 ≤ n) :
    finiteGlobalKernelSmoothEmbedding hπ data (j + 1) hnext hΔ i ≫
      finiteGlobalKernelClosureStep hπ data j hnext hΔ i =
        finiteGlobalKernelSmoothEmbedding hπ data j (Nat.le_of_succ_le hnext) hΔ i := by
  apply (cancel_mono
    (finiteGlobalKernelClosureInclusion hπ data j (Nat.le_of_succ_le hnext) hΔ i)).mp
  rw [Category.assoc, finiteGlobalKernelClosureStep_inclusion,
    finiteGlobalKernelSmoothEmbedding_inclusion_assoc,
    finiteGlobalSmoothEmbedding_step, finiteGlobalKernelSmoothEmbedding_inclusion]

end FLT.Mazur.WeierstrassDividedDepth
