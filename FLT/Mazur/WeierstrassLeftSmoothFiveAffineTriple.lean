/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothAffineTripleDescent

/-!
# Whole-cubic action associativity from five affine presentations

If the three inputs and the two intermediate sums lie in the affine chart,
associativity follows on the entire source scheme. No secant denominator,
reciprocal denominator or final-output coordinate needs to be selected.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Five actual affine presentations suffice for equality of the global triple sums. -/
theorem leftSmoothTripleAdd_of_fiveAffine {X : Scheme.{u}}
    (t : X ⟶ leftSmoothTriple W) (p q r s v : X ⟶ chartScheme W 2)
    (hp : p ≫ integralCurveChart W 2 = t ≫ leftSmoothTripleFirst W ≫ (integralSmoothOpen W).ι)
    (hq : q ≫ integralCurveChart W 2 = t ≫ leftSmoothTripleSecond W ≫ (integralSmoothOpen W).ι)
    (hr : r ≫ integralCurveChart W 2 = t ≫ leftSmoothTripleThird W)
    (hs : s ≫ integralCurveChart W 2 =
      t ≫ leftSmoothTriplePair W ≫ smoothFactorAddition W ≫ (integralSmoothOpen W).ι)
    (hv : v ≫ integralCurveChart W 2 =
      t ≫ leftSmoothTripleLastPair W ≫ leftSmoothFactorAddition W) :
    t ≫ leftSmoothTripleAddLeft W = t ≫ leftSmoothTripleAddRight W := by
  obtain ⟨a, ha⟩ := exists_affinePair_of_projections W
    (t ≫ leftSmoothTriplePair W ≫ smoothFactorsInclusion W) p q
    (by simpa only [smoothFactorsInclusion_fst,
      leftSmoothTripleFirst, Category.assoc] using hp)
    (by simpa only [smoothFactorsInclusion_snd,
      leftSmoothTripleSecond, Category.assoc] using hq)
  obtain ⟨b, hb⟩ := exists_affinePair_of_projections W
    (t ≫ leftSmoothTripleLastPair W ≫ leftSmoothFactorsInclusion W) q r
    (by simpa only [leftSmoothFactorsInclusion_fst,
      Category.assoc, leftSmoothTripleLastPair_fst_assoc] using hq)
    (by simpa only [leftSmoothFactorsInclusion_snd,
      Category.assoc, leftSmoothTripleLastPair_snd] using hr)
  obtain ⟨c, hc⟩ := exists_affinePair_of_projections W
    (t ≫ leftSmoothAddFirstPair W ≫ leftSmoothFactorsInclusion W) s r
    (by simpa only [leftSmoothFactorsInclusion_fst,
      Category.assoc, leftSmoothAddFirstPair_fst_assoc] using hs)
    (by simpa only [leftSmoothFactorsInclusion_snd,
      Category.assoc, leftSmoothAddFirstPair_snd] using hr)
  obtain ⟨d, hd⟩ := exists_affinePair_of_projections W
    (t ≫ leftSmoothAddLastPair W ≫ leftSmoothFactorsInclusion W) p v
    (by simpa only [leftSmoothFactorsInclusion_fst,
      Category.assoc, leftSmoothAddLastPair_fst_assoc] using hp)
    (by simpa only [leftSmoothFactorsInclusion_snd,
      Category.assoc, leftSmoothAddLastPair_snd] using hv)
  exact leftSmoothTripleAdd_of_affinePairs W t a b c d ha hb hc hd

end FLT.Mazur.WeierstrassIntegralChart
