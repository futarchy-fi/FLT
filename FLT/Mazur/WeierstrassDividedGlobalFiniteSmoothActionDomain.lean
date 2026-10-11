/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalFiniteActionProduct

/-!
# The complete original smooth input domain in the finite action product

The original smooth pair is an open immersion and the entire pullback of the
retained smooth embedding, not a selection of points or a generic-fiber chart.
This identifies exactly the input open where the action lift is constructed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace FLT.Mazur.WeierstrassDividedDepth

open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)

/-- The smooth pair is the full pullback of the actual original smooth embedding. -/
theorem finiteGlobalOriginalSmoothPair_isPullback :
    IsPullback (pullback.snd (integralSmoothStructure W) (integralSmoothStructure W))
      (finiteGlobalOriginalSmoothPair hπ data j hj)
      (finiteGlobalSmoothEmbedding hπ data j hj)
      (pullback.snd (integralSmoothStructure W) (finiteGlobalStructure hπ data j hj)) := by
  apply IsPullback.of_bot _ (finiteGlobalOriginalSmoothPair_snd hπ data j hj).symm
    (IsPullback.of_hasPullback (integralSmoothStructure W)
      (finiteGlobalStructure hπ data j hj)).flip
  simpa only [finiteGlobalOriginalSmoothPair_fst, finiteGlobalSmoothEmbedding_structure] using
    (IsPullback.of_hasPullback (integralSmoothStructure W) (integralSmoothStructure W)).flip

/-- The constructed action domain is an actual open subscheme of the entire input product. -/
instance finiteGlobalOriginalSmoothPair_isOpenImmersion :
    IsOpenImmersion (finiteGlobalOriginalSmoothPair hπ data j hj) :=
  MorphismProperty.of_isPullback (finiteGlobalOriginalSmoothPair_isPullback hπ data j hj)
    (inferInstanceAs (IsOpenImmersion (finiteGlobalSmoothEmbedding hπ data j hj)))

/-- Every input whose second coordinate contracts to the original smooth locus is retained. -/
theorem finiteGlobalOriginalSmoothPair_range :
    Set.range (finiteGlobalOriginalSmoothPair hπ data j hj) =
      (pullback.snd (integralSmoothStructure W) (finiteGlobalStructure hπ data j hj) ≫
        finiteGlobalContraction hπ data j hj) ⁻¹' (integralSmoothOpen W : Set _) := by
  change Set.range (finiteGlobalOriginalSmoothPair hπ data j hj) =
    (pullback.snd (integralSmoothStructure W) (finiteGlobalStructure hπ data j hj)) ⁻¹'
      (finiteGlobalContraction hπ data j hj) ⁻¹' (integralSmoothOpen W : Set _)
  have h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (finiteGlobalOriginalSmoothPair_isPullback hπ data j hj) ⊤
  simpa [finiteGlobalSmoothEmbedding_range] using congrArg SetLike.coe h

end FLT.Mazur.WeierstrassDividedDepth
