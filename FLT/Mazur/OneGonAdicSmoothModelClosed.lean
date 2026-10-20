/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicAlgebraicSmoothModel

/-!
# The enlarged smooth factor is a closed embedding

The fixed closed character embedding stays closed under coefficient enlargement.
Its smooth factor is therefore closed as well, and the full whole-cubic ideal
is exactly the pullback of the initial finite coefficient ideal.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]

/-- The enlarged embedding is Cartesian over the fixed initial closed embedding. -/
theorem smoothModelEmbedding_isPullback :
    IsPullback (smoothModelEmbedding I t ht n).left
      (pullback.fst (algebraicCarrier I t ht n).hom (smoothModelBaseMap I t ht n))
      (pullback.fst (algebraicCurve I t ht n).curve.hom (smoothModelBaseMap I t ht n))
      (algebraicEmbedding I t ht n) :=
  OverPullbackLocalPushout.map_isPullback (smoothModelBaseMap I t ht n)
    (Over.homMk (algebraicEmbedding I t ht n) (algebraicEmbedding_structure I t ht n))

instance smoothModelEmbedding_isClosedImmersion :
    IsClosedImmersion (smoothModelEmbedding I t ht n).left :=
  MorphismProperty.of_isPullback (smoothModelEmbedding_isPullback I t ht n).flip
    (inferInstanceAs (IsClosedImmersion (algebraicEmbedding I t ht n)))

/-- The descended smooth factor is a closed immersion in the entire smooth group. -/
instance smoothModelFactor_isClosedImmersion :
    IsClosedImmersion (smoothModelFactor I t ht n).left := by
  let _ : IsClosedImmersion
      ((smoothModelFactor I t ht n).left ≫ (smoothModelCurve I t ht n).inclusion.left) := by
    change IsClosedImmersion
      (smoothModelFactor I t ht n ≫ (smoothModelCurve I t ht n).inclusion).left
    rw [smoothModelFactor_inclusion]
    infer_instance
  exact IsClosedImmersion.of_comp _ (smoothModelCurve I t ht n).inclusion.left

/-- Enlargement retains the full original model ideal without taking a radical. -/
theorem smoothModelEmbedding_ideal :
    (smoothModelEmbedding I t ht n).left.ker =
      (algebraicEmbedding I t ht n).ker.comap
        (pullback.fst (algebraicCurve I t ht n).curve.hom (smoothModelBaseMap I t ht n)) := by
  rw [← (smoothModelEmbedding_isPullback I t ht n).isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]
  exact Scheme.IdealSheafData.ker_fst_of_isClosedImmersion _ _

end FLT.Mazur.OneGonAdicCharacterTower
