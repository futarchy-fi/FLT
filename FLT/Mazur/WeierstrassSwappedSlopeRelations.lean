/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineProductSwap
public import FLT.Mazur.WeierstrassAdditionSlopeFamilies

/-!
# Both slope families satisfy the original relations after swapping inputs

On an arbitrary common coefficient algebra the original input map and the
swapped chart restriction determine the same two line relations. The
explicit changes of tangent numerator and denominator cancel by the first
relation, including over rings with zero divisors.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (b : Bool) (f : AffineProduct W →ₐ[R] S)

/-- A swapped ordinary chart retains the original line relation. -/
theorem ordinaryChartSlope_swapped_line
    (g : additionChartRing W (ordinaryIndex b) →ₐ[R] S)
    (hbase : g.comp (additionChartAlgRestriction W (ordinaryIndex b)) =
      f.comp (affineProductSwap W)) :
    g (ordinaryChartSlope W b) * f (secantDenominator W) =
      f (verticalSecantDenominator W) := by
  have hb (a) : g (additionChartAlgRestriction W (ordinaryIndex b) a) =
      f (affineProductSwap W a) := DFunLike.congr_fun hbase a
  have hl := congrArg g (ordinaryChartSlope_line W b)
  simp only [map_mul, hb, affineProductSwap_secantDenominator,
    affineProductSwap_verticalSecantDenominator, map_neg] at hl
  linear_combination -hl

/-- A swapped ordinary chart retains the original divided-difference relation. -/
theorem ordinaryChartSlope_swapped_cubic
    (g : additionChartRing W (ordinaryIndex b) →ₐ[R] S)
    (hbase : g.comp (additionChartAlgRestriction W (ordinaryIndex b)) =
      f.comp (affineProductSwap W)) :
    g (ordinaryChartSlope W b) * f (tangentDenominator W) = f (tangentNumerator W) := by
  have hb (a) : g (additionChartAlgRestriction W (ordinaryIndex b) a) =
      f (affineProductSwap W a) := DFunLike.congr_fun hbase a
  have hc := congrArg g (ordinaryChartSlope_cubic W b)
  simp only [map_mul, hb, affineProductSwap_tangentDenominator,
    affineProductSwap_tangentNumerator, map_add, AlgHom.commutes] at hc
  linear_combination hc - algebraMap R S W.a₁ *
    ordinaryChartSlope_swapped_line W b f g hbase

/-- A swapped reciprocal chart retains the reversed line relation. -/
theorem reciprocalChartSlope_swapped_line
    (g : additionChartRing W (reciprocalIndex b) →ₐ[R] S)
    (hbase : g.comp (additionChartAlgRestriction W (reciprocalIndex b)) =
      f.comp (affineProductSwap W)) :
    g (reciprocalChartSlope W b) * f (verticalSecantDenominator W) =
      f (secantDenominator W) := by
  have hb (a) : g (additionChartAlgRestriction W (reciprocalIndex b) a) =
      f (affineProductSwap W a) := DFunLike.congr_fun hbase a
  have hl := congrArg g (reciprocalChartSlope_line W b)
  simp only [map_mul, hb, affineProductSwap_secantDenominator,
    affineProductSwap_verticalSecantDenominator, map_neg] at hl
  linear_combination -hl

/-- A swapped reciprocal chart retains the reversed divided-difference relation. -/
theorem reciprocalChartSlope_swapped_cubic
    (g : additionChartRing W (reciprocalIndex b) →ₐ[R] S)
    (hbase : g.comp (additionChartAlgRestriction W (reciprocalIndex b)) =
      f.comp (affineProductSwap W)) :
    g (reciprocalChartSlope W b) * f (tangentNumerator W) = f (tangentDenominator W) := by
  have hb (a) : g (additionChartAlgRestriction W (reciprocalIndex b) a) =
      f (affineProductSwap W a) := DFunLike.congr_fun hbase a
  have hc := congrArg g (reciprocalChartSlope_cubic W b)
  simp only [map_mul, hb, affineProductSwap_tangentDenominator,
    affineProductSwap_tangentNumerator, map_add, AlgHom.commutes] at hc
  linear_combination hc - algebraMap R S W.a₁ *
    reciprocalChartSlope_swapped_line W b f g hbase

end FLT.Mazur.WeierstrassIntegralChart
