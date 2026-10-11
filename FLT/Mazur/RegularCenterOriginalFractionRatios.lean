/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.RegularCenterQuotientLinear
public import FLT.Mazur.BlowupFractionChartRatio

/-!
# Quotient identities for original fraction lifts

Any original fraction-chart map extending the actual coordinate map has the
same quotient identities. This compares concrete geometric lifts directly
with conormal calculations in an intermediate coefficient algebra.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.RegularCenter
open BlowupFractionChart
variable {A S B : Type*} [CommRing A] [CommRing S] [CommRing B]
  (I : Ideal A) (J : Ideal S) (f : A →+* S) (φ : S →+* B)
  (z : B) (hJ : J.map φ = Ideal.span {z}) (hz : IsRegular z)
  (a : A) (ha : f a ∈ J) (L : chart I a →+* B)
  (hL : ∀ t, L (algebraMap A (chart I a) t) = φ (f t))

include hz hL in
/-- A lift of the original chart has the ratios computed in the actual pulled-back center. -/
theorem originalLift_ratio_quotient (b : A) (hb : b ∈ I) (hfb : f b ∈ J) :
    quotient J φ z hJ (f a) ha * L (ratio I a b hb) =
      quotient J φ z hJ (f b) hfb := by
  apply hz.left
  dsimp only
  rw [← mul_assoc, denominator_mul_quotient, denominator_mul_quotient, ← hL a]
  change L (denominator I a) * L (ratio I a b hb) = _
  rw [← map_mul, denominator_mul_ratio, hL]

end FLT.Mazur.RegularCenter
