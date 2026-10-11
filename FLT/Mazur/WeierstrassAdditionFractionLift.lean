/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAdditionCenterContainment
public import FLT.Mazur.BlowupFractionChartMap

/-!
# First actual fraction-chart lifts of integral addition

The ordinary and polynomial action maps lift to the original Rees fraction
algebras at the actual image of each output denominator. Their contractions
are the original addition maps. Covering the complete modified input and
gluing these maps on the exceptional overlaps are separate constructions.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4)

/-- The ordinary law lifts to an actual fraction chart of the unchanged input center. -/
def ordinaryAdditionFractionLift (b : Bool) (d : Coordinate W 2) :
    BlowupFractionChart.chart (modificationChartCenter W s 2) d →+*
      BlowupFractionChart.chart
        ((modificationChartCenter W s 2).map (ordinaryInputRight W b).toRingHom)
        (ordinaryChartAddition W b d) :=
  BlowupFractionChart.chartMap _ _ (ordinaryChartAddition W b).toRingHom
    (ordinarySpecialization_center_le W s b (AlgHom.id R _) b3 b4 h3 h4) d

/-- The ordinary lifted map contracts to precisely the original ordinary addition. -/
theorem ordinaryAdditionFractionLift_base (b : Bool) (d a : Coordinate W 2) :
    ordinaryAdditionFractionLift W s b3 b4 h3 h4 b d (algebraMap _ _ a) =
      algebraMap _ _ (ordinaryChartAddition W b a) :=
  BlowupFractionChart.chartMap_base _ _ _ _ _ _

/-- Every actual ordinary output-center ratio retains its original action numerator. -/
theorem ordinaryAdditionFractionLift_ratio (b : Bool) (d a : Coordinate W 2)
    (ha : a ∈ modificationChartCenter W s 2) :
    ordinaryAdditionFractionLift W s b3 b4 h3 h4 b d
        (BlowupFractionChart.ratio _ d a ha) =
      BlowupFractionChart.ratio _ (ordinaryChartAddition W b d) (ordinaryChartAddition W b a)
        ((ordinarySpecialization_center_le W s b (AlgHom.id R _) b3 b4 h3 h4)
          (Ideal.mem_map_of_mem (ordinaryChartAddition W b).toRingHom ha)) :=
  BlowupFractionChart.chartMap_ratio _ _ _ _ _ _ _

/-- The polynomial law lifts over every original projective input and output chart. -/
def projectiveAdditionFractionLift (j k t : Fin 3) (b6 : R) (h6 : W.a₆ = s * b6)
    (d : Coordinate W t) :
    BlowupFractionChart.chart (modificationChartCenter W s t) d →+*
      BlowupFractionChart.chart
        ((modificationChartCenter W s k).map
          ((additionOutputRestriction W j k t).comp (chartProductRight W j k)).toRingHom)
        (projectiveAdditionChart W j k t d) :=
  BlowupFractionChart.chartMap _ _ (projectiveAdditionChart W j k t).toRingHom
    (projectiveSpecialization_center_le W s j k t (AlgHom.id R _) b3 b4 b6 h3 h4 h6) d

/-- Polynomial fraction lifts retain the original contraction on every coordinate function. -/
theorem projectiveAdditionFractionLift_base (j k t : Fin 3)
    (b6 : R) (h6 : W.a₆ = s * b6) (d a : Coordinate W t) :
    projectiveAdditionFractionLift W s b3 b4 h3 h4 j k t b6 h6 d (algebraMap _ _ a) =
      algebraMap _ _ (projectiveAdditionChart W j k t a) :=
  BlowupFractionChart.chartMap_base _ _ _ _ _ _

end FLT.Mazur.WeierstrassIntegralChart
