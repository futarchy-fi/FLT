/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineNegationAddition

/-!
# Ordinary addition domains vanish along point-negation pairs

The ordinary denominator becomes zero on the actual point-negation section.
Since it is a unit on either ordinary domain, every common algebra is the zero
ring. This statement includes nonreduced algebras and needs no discriminant assumption.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- The denominator of either ordinary addition chart vanishes on the negation pair. -/
theorem affineNegationPair_ordinaryDenominator (b : Bool) :
    affineNegationPair W (if b then tangentDenominator W else secantDenominator W) = 0 := by
  cases b
  · exact affineNegationPair_secantDenominator W
  · exact affineNegationPair_tangentDenominator W

/-- An algebra over an ordinary addition domain and the negation pair is the zero ring. -/
theorem ordinaryChart_negation_subsingleton (b : Bool)
    (f : additionChartRing W (ordinaryIndex b) →ₐ[R] S) (g : Coordinate W 2 →ₐ[R] S)
    (h : f.comp (additionChartAlgRestriction W (ordinaryIndex b)) =
      g.comp (affineNegationPair W)) : Subsingleton S := by
  have hu := (ordinaryChartDenominator_isUnit W b).map f
  have he := DFunLike.congr_fun h
    (if b then tangentDenominator W else secantDenominator W)
  change f (additionChartAlgRestriction W (ordinaryIndex b) _) = g _ at he
  have hz := he.trans ((congrArg g (affineNegationPair_ordinaryDenominator W b)).trans
    (map_zero g))
  rw [hz] at hu
  exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hu)

end FLT.Mazur.WeierstrassIntegralChart
