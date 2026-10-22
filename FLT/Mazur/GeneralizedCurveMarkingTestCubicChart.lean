/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingTestCover
public import FLT.Mazur.GeneralizedCurveMarkingTestEquation
public import FLT.Mazur.CartesianFiniteFibers

/-!
# Concrete cubic chart inclusions over arbitrary test schemes

Actual coefficient equations over factored affine test neighborhoods map
openly into the pulled-back global cubic. Their images are exactly the
inverse images of the original test opens, with categorical recovery.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} [IsLocallyNoetherian S] (E : GeneralizedEllipticCurve S)
  (s : 𝟙_ (Over S) ⟶ E.group) (g : T ⟶ S) (c : SmoothMarkingTestChart E s g)

/-- The original coefficient equation on an actual affine test neighborhood. -/
def smoothMarkingTestChartEquation : WeierstrassCurve Γ(c.base.1.toScheme, ⊤) :=
  smoothMarkingTestEquation E s c.original c.map

/-- The coefficient cubic has the original whole-base cartesian square. -/
theorem smoothMarkingTestChart_original_isPullback :
    IsPullback
      (affineIntegralCoefficient (smoothMarkingAffineEquation E s c.original) c.map ≫
        smoothMarkingGluedChart E s c.original)
      (affineIntegralStructure (smoothMarkingTestChartEquation E s g c))
      (smoothMarkingGluedBase E s) (c.base.1.ι ≫ g) := by
  rw [← c.fac]
  exact (affineIntegralCoefficient_isPullback
    (smoothMarkingAffineEquation E s c.original) c.map).paste_horiz
      (smoothMarkingGluedChart_isPullback E s c.original).flip

/-- The actual coefficient cubic chart inclusion into the whole test cubic. -/
def smoothMarkingTestChartMap : integralCurve (smoothMarkingTestChartEquation E s g c) ⟶
    smoothMarkingPulledCubic E s g :=
  Limits.pullback.lift
    (affineIntegralCoefficient (smoothMarkingAffineEquation E s c.original) c.map ≫
      smoothMarkingGluedChart E s c.original)
    (affineIntegralStructure (smoothMarkingTestChartEquation E s g c) ≫ c.base.1.ι)
    ((smoothMarkingTestChart_original_isPullback E s g c).w.trans
      (Category.assoc _ _ _).symm)

/-- Projection retains the original coefficient map and original chart. -/
@[reassoc] theorem smoothMarkingTestChartMap_projection :
    smoothMarkingTestChartMap E s g c ≫ smoothMarkingPulledProjection E s g =
      affineIntegralCoefficient (smoothMarkingAffineEquation E s c.original) c.map ≫
        smoothMarkingGluedChart E s c.original := Limits.pullback.lift_fst _ _ _

/-- The concrete chart lies over its actual original test open. -/
@[reassoc] theorem smoothMarkingTestChartMap_over :
    smoothMarkingTestChartMap E s g c ≫ smoothMarkingPulledBase E s g =
      affineIntegralStructure (smoothMarkingTestChartEquation E s g c) ≫ c.base.1.ι :=
  Limits.pullback.lift_snd _ _ _

/-- The concrete equation is the categorical restriction to the actual test open. -/
theorem smoothMarkingTestChart_isPullback :
    IsPullback (smoothMarkingTestChartMap E s g c)
      (affineIntegralStructure (smoothMarkingTestChartEquation E s g c))
      (smoothMarkingPulledBase E s g) c.base.1.ι := by
  have H : IsPullback
      (smoothMarkingTestChartMap E s g c ≫ smoothMarkingPulledProjection E s g)
      (affineIntegralStructure (smoothMarkingTestChartEquation E s g c))
      (smoothMarkingGluedBase E s) (c.base.1.ι ≫ g) := by
    rw [smoothMarkingTestChartMap_projection]
    exact smoothMarkingTestChart_original_isPullback E s g c
  exact H.of_right (smoothMarkingTestChartMap_over E s g c)
    (smoothMarkingPulled_isPullback E s g)

/-- Every actual coefficient chart maps openly into the whole test cubic. -/
instance smoothMarkingTestChartMap_isOpenImmersion :
    IsOpenImmersion (smoothMarkingTestChartMap E s g c) :=
  MorphismProperty.of_isPullback (smoothMarkingTestChart_isPullback E s g c).flip
    inferInstance

/-- The actual chart image is precisely the inverse image of the original test open. -/
theorem smoothMarkingTestChartMap_range :
    Set.range (smoothMarkingTestChartMap E s g c) =
      smoothMarkingPulledBase E s g ⁻¹' (c.base.1 : Set T) := by
  rw [CartesianFiniteFibers.range_eq_preimage
    (smoothMarkingTestChart_isPullback E s g c).flip, Scheme.Opens.range_ι]

end FLT.Mazur.GeneralizedEllipticCurve
