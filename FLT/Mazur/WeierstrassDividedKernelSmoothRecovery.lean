/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedKernelSmoothEmbedding

/-!
# Exact recovery of the original smooth kernel inside the divided closure

The original smooth kernel is precisely the inverse image of the retained
original smooth ambient scheme. Schematic density identifies the two closed
subschemes, proving that the constructed embedding is an open immersion.
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

/-- The original generic source in the actual smooth inverse image of the divided closure. -/
def finiteGlobalKernelToSmoothPullback : H ⟶
    pullback (finiteGlobalKernelClosureInclusion hπ data j hj hΔ i)
      (finiteGlobalSmoothEmbedding hπ data j hj) :=
  genericKernelToClosureSmooth W hΔ i ≫ finiteGlobalKernelSmoothComparison hπ data j hj hΔ i

/-- This generic source is the pullback of the full dense generic source along an open map. -/
theorem finiteGlobalKernelToSmoothPullback_isPullback :
    IsPullback (𝟙 _) (finiteGlobalKernelToSmoothPullback hπ data j hj hΔ i)
      (finiteGlobalKernelToClosure hπ data j hj hΔ i)
      (pullback.fst (finiteGlobalKernelClosureInclusion hπ data j hj hΔ i)
        (finiteGlobalSmoothEmbedding hπ data j hj)) := by
  apply IsPullback.of_horiz_isIso_mono
  constructor
  rw [Category.id_comp, finiteGlobalKernelToSmoothPullback,
    Category.assoc, finiteGlobalKernelSmoothComparison_fst,
    genericKernelToClosureSmooth_dividedEmbedding]

instance finiteGlobalKernelToSmoothPullback_dense :
    IsSchemeTheoreticallyDominant (finiteGlobalKernelToSmoothPullback hπ data j hj hΔ i) :=
  IsSchemeTheoreticallyDominant.of_isPullback
    (finiteGlobalKernelToSmoothPullback_isPullback hπ data j hj hΔ i)

instance finiteGlobalKernelSmoothComparison_dense :
    IsSchemeTheoreticallyDominant (finiteGlobalKernelSmoothComparison hπ data j hj hΔ i) := by
  constructor
  have he := (finiteGlobalKernelToSmoothPullback hπ data j hj hΔ i).ker_eq_bot
  simpa only [finiteGlobalKernelToSmoothPullback, Scheme.Hom.ker_comp,
    Scheme.Hom.ker_eq_bot, Scheme.IdealSheafData.map_bot] using he

instance finiteGlobalKernelSmoothComparison_closed :
    IsClosedImmersion (finiteGlobalKernelSmoothComparison hπ data j hj hΔ i) := by
  let _ : IsClosedImmersion (finiteGlobalKernelSmoothComparison hπ data j hj hΔ i ≫
      pullback.snd _ _) := by
    rw [finiteGlobalKernelSmoothComparison_snd]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (pullback.snd _ _)

instance finiteGlobalKernelSmoothComparison_isIso :
    IsIso (finiteGlobalKernelSmoothComparison hπ data j hj hΔ i) :=
  IsClosedImmersion.isIso_iff_ker_eq_bot.mpr
    (finiteGlobalKernelSmoothComparison hπ data j hj hΔ i).ker_eq_bot

/-- The exact original smooth kernel is the entire inverse image of the retained smooth open. -/
theorem finiteGlobalKernelSmoothEmbedding_isPullback :
    IsPullback (finiteGlobalKernelSmoothEmbedding hπ data j hj hΔ i)
      (genericClosureSmoothInclusion W i) (finiteGlobalKernelClosureInclusion hπ data j hj hΔ i)
      (finiteGlobalSmoothEmbedding hπ data j hj) :=
  IsPullback.of_iso_pullback ⟨finiteGlobalKernelSmoothEmbedding_inclusion hπ data j hj hΔ i⟩
    (asIso (finiteGlobalKernelSmoothComparison hπ data j hj hΔ i))
    (finiteGlobalKernelSmoothComparison_fst hπ data j hj hΔ i)
    (finiteGlobalKernelSmoothComparison_snd hπ data j hj hΔ i)

instance finiteGlobalKernelSmoothEmbedding_open :
    IsOpenImmersion (finiteGlobalKernelSmoothEmbedding hπ data j hj hΔ i) :=
  MorphismProperty.of_isPullback
    (finiteGlobalKernelSmoothEmbedding_isPullback hπ data j hj hΔ i).flip
    (inferInstanceAs (IsOpenImmersion (finiteGlobalSmoothEmbedding hπ data j hj)))

end FLT.Mazur.WeierstrassDividedDepth
