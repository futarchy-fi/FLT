/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineTripleDescent

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
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- Five actual affine presentations suffice for equality of the global triple sums. -/
theorem integralCurveTripleAdd_of_fiveAffine {X : Scheme.{u}}
    (t : X ⟶ integralCurveTriple W) (p q r s v : X ⟶ chartScheme W 2)
    (hp : p ≫ integralCurveChart W 2 = t ≫ integralCurveTripleFirst W)
    (hq : q ≫ integralCurveChart W 2 = t ≫ integralCurveTripleSecond W)
    (hr : r ≫ integralCurveChart W 2 = t ≫ integralCurveTripleThird W)
    (hs : s ≫ integralCurveChart W 2 =
      t ≫ integralCurveTriplePair W ≫ integralCurveAddition W hΔ)
    (hv : v ≫ integralCurveChart W 2 =
      t ≫ integralCurveTripleLastPair W ≫ integralCurveAddition W hΔ) :
    t ≫ integralCurveTripleAddLeft W hΔ = t ≫ integralCurveTripleAddRight W hΔ := by
  obtain ⟨a, ha⟩ := exists_affinePair_of_projections W (t ≫ integralCurveTriplePair W) p q
    (by simpa only [integralCurveTripleFirst, Category.assoc] using hp)
    (by simpa only [integralCurveTripleSecond, Category.assoc] using hq)
  obtain ⟨b, hb⟩ := exists_affinePair_of_projections W (t ≫ integralCurveTripleLastPair W) q r
    (by simpa only [Category.assoc, integralCurveTripleLastPair_fst] using hq)
    (by simpa only [Category.assoc, integralCurveTripleLastPair_snd] using hr)
  obtain ⟨c, hc⟩ := exists_affinePair_of_projections W (t ≫ integralCurveAddFirstPair W hΔ) s r
    (by simpa only [Category.assoc, integralCurveAddFirstPair_fst] using hs)
    (by simpa only [Category.assoc, integralCurveAddFirstPair_snd] using hr)
  obtain ⟨d, hd⟩ := exists_affinePair_of_projections W (t ≫ integralCurveAddLastPair W hΔ) p v
    (by simpa only [Category.assoc, integralCurveAddLastPair_fst] using hp)
    (by simpa only [Category.assoc, integralCurveAddLastPair_snd] using hv)
  exact integralCurveTripleAdd_of_affinePairs W hΔ t a b c d ha hb hc hd

end FLT.Mazur.WeierstrassIntegralChart
