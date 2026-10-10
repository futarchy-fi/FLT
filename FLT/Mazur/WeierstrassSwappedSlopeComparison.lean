/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSwappedSlopeRelations
public import FLT.Mazur.WeierstrassAffineNegationAddition
public import FLT.Mazur.WeierstrassSlopeSwapFormula

/-!
# Comparing slopes and ordinary outputs with reversed inputs

On every common algebra the same-family slopes agree and the mixed-family
slopes are inverse, using only the existing denominator units. The ordinary
addition algebra maps themselves then agree with reversed inputs.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassIntegralAddition

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (b c : Bool)

/-- Any two ordinary charts with reversed inputs have equal slopes. -/
theorem ordinaryChartSlopes_swap
    (f : additionChartRing W (ordinaryIndex b) →ₐ[R] S)
    (g : additionChartRing W (ordinaryIndex c) →ₐ[R] S)
    (hbase : g.comp (additionChartAlgRestriction W (ordinaryIndex c)) =
      (f.comp (additionChartAlgRestriction W (ordinaryIndex b))).comp (affineProductSwap W)) :
    f (ordinaryChartSlope W b) = g (ordinaryChartSlope W c) := by
  have hu := (ordinaryChartDenominator_isUnit W b).map f
  cases b
  · have hf := congrArg f (ordinaryChartSlope_line W false)
    have hg := ordinaryChartSlope_swapped_line W c _ g hbase
    simp only [map_mul] at hf
    exact hu.mul_left_inj.mp (hf.trans hg.symm)
  · have hf := congrArg f (ordinaryChartSlope_cubic W true)
    have hg := ordinaryChartSlope_swapped_cubic W c _ g hbase
    simp only [map_mul] at hf
    exact hu.mul_left_inj.mp (hf.trans hg.symm)

/-- Any two reciprocal charts with reversed inputs have equal slopes. -/
theorem reciprocalChartSlopes_swap
    (f : additionChartRing W (reciprocalIndex b) →ₐ[R] S)
    (g : additionChartRing W (reciprocalIndex c) →ₐ[R] S)
    (hbase : g.comp (additionChartAlgRestriction W (reciprocalIndex c)) =
      (f.comp (additionChartAlgRestriction W (reciprocalIndex b))).comp (affineProductSwap W)) :
    f (reciprocalChartSlope W b) = g (reciprocalChartSlope W c) := by
  have hu := (reciprocalChartDenominator_isUnit W b).map f
  cases b
  · have hf := congrArg f (reciprocalChartSlope_line W false)
    have hg := reciprocalChartSlope_swapped_line W c _ g hbase
    simp only [map_mul] at hf
    exact hu.mul_left_inj.mp (hf.trans hg.symm)
  · have hf := congrArg f (reciprocalChartSlope_cubic W true)
    have hg := reciprocalChartSlope_swapped_cubic W c _ g hbase
    simp only [map_mul] at hf
    exact hu.mul_left_inj.mp (hf.trans hg.symm)

/-- Mixed ordinary and reciprocal charts with reversed inputs have inverse slopes. -/
theorem mixedChartSlopes_swap_inverse
    (f : additionChartRing W (ordinaryIndex b) →ₐ[R] S)
    (g : additionChartRing W (reciprocalIndex c) →ₐ[R] S)
    (hbase : g.comp (additionChartAlgRestriction W (reciprocalIndex c)) =
      (f.comp (additionChartAlgRestriction W (ordinaryIndex b))).comp (affineProductSwap W)) :
    g (reciprocalChartSlope W c) * f (ordinaryChartSlope W b) = 1 := by
  have hu := (ordinaryChartDenominator_isUnit W b).map f
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hu
  · apply inverse_slopes_of_relations hu
    · simpa only [map_mul] using congrArg f (ordinaryChartSlope_line W false)
    · exact reciprocalChartSlope_swapped_line W c _ g hbase
  · apply inverse_slopes_of_relations hu
    · simpa only [map_mul] using congrArg f (ordinaryChartSlope_cubic W true)
    · exact reciprocalChartSlope_swapped_cubic W c _ g hbase

/-- The actual ordinary output algebra maps agree on every algebra with reversed inputs. -/
theorem ordinaryChartAddition_swap
    (f : additionChartRing W (ordinaryIndex b) →ₐ[R] S)
    (g : additionChartRing W (ordinaryIndex c) →ₐ[R] S)
    (hbase : g.comp (additionChartAlgRestriction W (ordinaryIndex c)) =
      (f.comp (additionChartAlgRestriction W (ordinaryIndex b))).comp (affineProductSwap W)) :
    f.comp (ordinaryChartAddition W b) = g.comp (ordinaryChartAddition W c) := by
  have hb (a) : g (additionChartAlgRestriction W (ordinaryIndex c) a) =
      f (additionChartAlgRestriction W (ordinaryIndex b) (affineProductSwap W a)) :=
    DFunLike.congr_fun hbase a
  have hs := ordinaryChartSlopes_swap W b c f g hbase
  have hl := congrArg f (ordinaryChartSlope_line W b)
  simp only [map_mul, secantDenominator, verticalSecantDenominator, map_sub] at hl
  apply hom_ext
  intro i
  change f (ordinaryChartAddition W b (coord W 2 i)) =
    g (ordinaryChartAddition W c (coord W 2 i))
  rw [ordinaryChartAddition_map_coord, ordinaryChartAddition_map_coord]
  simp only [hb, affineProductSwap_x₁, affineProductSwap_x₂, affineProductSwap_y₁, ← hs]
  exact (congrFun (ordinaryAdditionXYZ_swap (W.map (algebraMap R S)) hl) i).symm

end FLT.Mazur.WeierstrassIntegralChart
