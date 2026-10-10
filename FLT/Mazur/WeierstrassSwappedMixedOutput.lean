/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSwappedReciprocalOutput
public import FLT.Mazur.WeierstrassMixedOutputComparison

/-!
# The output transition on reversed ordinary/reciprocal inputs

For all four reversed mixed pairs the output factor is a unit, and the reciprocal
output lifts to the Y/Z overlap. The transition of this lift is exactly the
ordinary output, over every common algebra of the two actual domains.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassIntegralAddition

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (b c : Bool)
  (f : additionChartRing W (ordinaryIndex b) →ₐ[R] S)
  (g : additionChartRing W (reciprocalIndex c) →ₐ[R] S)
  (hbase : g.comp (additionChartAlgRestriction W (reciprocalIndex c)) =
    (f.comp (additionChartAlgRestriction W (ordinaryIndex b))).comp (affineProductSwap W))

include hbase in
/-- The output factor is a unit on the whole mixed intersection. -/
theorem swappedMixedOutputScale_isUnit : IsUnit (mixedOutputScale W c g) := by
  have hm : IsUnit (g (reciprocalChartSlope W c)) :=
    isUnit_iff_exists_inv.mpr ⟨_, mixedChartSlopes_swap_inverse W b c f g hbase⟩
  exact ((reciprocalChartInverse_isUnit W c).map g).mul (hm.pow 3)

include hbase in
/-- Every normalized reciprocal coordinate is the same unit times its ordinary coordinate. -/
theorem swappedMixedOutput_scaled (i : Fin 3) :
    g (reciprocalChartAddition W c (coord W 1 i)) =
      mixedOutputScale W c g * f (ordinaryChartAddition W b (coord W 2 i)) := by
  have hb (a) := DFunLike.congr_fun hbase a
  simp only [AlgHom.comp_apply] at hb
  have hl := reciprocalChartSlope_swapped_line W c _ g hbase
  simp only [AlgHom.comp_apply, verticalSecantDenominator, secantDenominator, map_sub] at hl
  rw [reciprocalChartAddition_coord, map_mul, reciprocalCoordinates_map]
  dsimp only [reciprocalCoordinates, AlgHom.comp_apply]
  simp only [hb, affineProductSwap_x₁, affineProductSwap_x₂, affineProductSwap_y₁]
  rw [reciprocalAdditionXYZ_swap (W.map (algebraMap R S)) hl]
  have hs := congrFun (reciprocalXYZ_eq_scaled_add (W.map (algebraMap R S))
    (f (additionChartAlgRestriction W (ordinaryIndex b) (productX₁ W)))
    (f (additionChartAlgRestriction W (ordinaryIndex b) (productX₂ W)))
    (f (additionChartAlgRestriction W (ordinaryIndex b) (productY₁ W)))
    (f (ordinaryChartSlope W b)) (g (reciprocalChartSlope W c))
    (mixedChartSlopes_swap_inverse W b c f g hbase)) i
  change g (reciprocalChartInverse W c) *
      reciprocalXYZ _ _ _ _ _ i = _
  rw [hs, ordinaryChartAddition_map_coord]
  exact (mul_assoc _ _ _).symm

/-- The mixed comparison factors through the actual integral output overlap. -/
def swappedMixedOutputLift : Overlap W 1 2 →ₐ[R] S :=
  scaledChartLift W 2 1 (f.comp (ordinaryChartAddition W b))
    (g.comp (reciprocalChartAddition W c)) (mixedOutputScale W c g)
    (swappedMixedOutputScale_isUnit W b c f g hbase) (swappedMixedOutput_scaled W b c f g hbase)

/-- Restricting the overlap lift to the Y-chart gives the reciprocal law. -/
theorem swappedMixedOutputLift_restriction :
    (swappedMixedOutputLift W b c f g hbase).comp (overlapRestriction W 1 2) =
      g.comp (reciprocalChartAddition W c) :=
  scaledChartLift_restriction W 2 1 _ _ _ _ _

/-- Changing the lifted reciprocal output to the Z-chart gives the ordinary law. -/
theorem swappedMixedOutputLift_transition :
    (swappedMixedOutputLift W b c f g hbase).comp (transitionBase W 1 2) =
      f.comp (ordinaryChartAddition W b) :=
  scaledChartLift_transition W 2 1 _ _ _ _ _

end FLT.Mazur.WeierstrassIntegralChart
