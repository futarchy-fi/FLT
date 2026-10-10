/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothAffineTripleDescent

/-!
# Associativity from five affine presentations

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
theorem smoothFactorTripleAdd_of_fiveAffine {X : Scheme.{u}}
    (t : X ⟶ smoothFactorTriple W) (p q r s v : X ⟶ chartScheme W 2)
    (hp : p ≫ integralCurveChart W 2 = t ≫ smoothFactorTripleFirst W ≫ (integralSmoothOpen W).ι)
    (hq : q ≫ integralCurveChart W 2 = t ≫ smoothFactorTripleSecond W ≫ (integralSmoothOpen W).ι)
    (hr : r ≫ integralCurveChart W 2 = t ≫ smoothFactorTripleThird W ≫ (integralSmoothOpen W).ι)
    (hs : s ≫ integralCurveChart W 2 =
      t ≫ smoothFactorTriplePair W ≫ smoothFactorAddition W ≫ (integralSmoothOpen W).ι)
    (hv : v ≫ integralCurveChart W 2 =
      t ≫ smoothFactorTripleLastPair W ≫ smoothFactorAddition W ≫ (integralSmoothOpen W).ι) :
    t ≫ smoothFactorTripleAddLeft W = t ≫ smoothFactorTripleAddRight W := by
  obtain ⟨a, ha⟩ := exists_affinePair_of_projections W
    (t ≫ smoothFactorTriplePair W ≫ smoothFactorsInclusion W) p q
    (by simpa only [smoothFactorsInclusion_fst,
      smoothFactorTripleFirst, Category.assoc] using hp)
    (by simpa only [smoothFactorsInclusion_snd,
      smoothFactorTripleSecond, Category.assoc] using hq)
  obtain ⟨b, hb⟩ := exists_affinePair_of_projections W
    (t ≫ smoothFactorTripleLastPair W ≫ smoothFactorsInclusion W) q r
    (by simpa only [smoothFactorsInclusion_fst,
      Category.assoc, smoothFactorTripleLastPair_fst_assoc] using hq)
    (by simpa only [smoothFactorsInclusion_snd,
      Category.assoc, smoothFactorTripleLastPair_snd_assoc] using hr)
  obtain ⟨c, hc⟩ := exists_affinePair_of_projections W
    (t ≫ smoothFactorAddFirstPair W ≫ smoothFactorsInclusion W) s r
    (by simpa only [smoothFactorsInclusion_fst,
      Category.assoc, smoothFactorAddFirstPair_fst_assoc] using hs)
    (by simpa only [smoothFactorsInclusion_snd,
      Category.assoc, smoothFactorAddFirstPair_snd_assoc] using hr)
  obtain ⟨d, hd⟩ := exists_affinePair_of_projections W
    (t ≫ smoothFactorAddLastPair W ≫ smoothFactorsInclusion W) p v
    (by simpa only [smoothFactorsInclusion_fst,
      Category.assoc, smoothFactorAddLastPair_fst_assoc] using hp)
    (by simpa only [smoothFactorsInclusion_snd,
      Category.assoc, smoothFactorAddLastPair_snd_assoc] using hv)
  exact smoothFactorTripleAdd_of_affinePairs W t a b c d ha hb hc hd

end FLT.Mazur.WeierstrassIntegralChart
