/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothTripleProjections
public import FLT.Mazur.WeierstrassSmoothAdditionOutputRegular

/-!
# Regular coordinates of the three action inputs and their first sum

The unrestricted third input has regular Z because its original projection is
flat. The first sum uses the existing smooth law on the first two inputs.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The first smooth input has regular Z on every flat Y/Z presentation. -/
theorem leftSmoothTripleFirst_z_regular {X : Scheme.{u}}
    (t : X ⟶ leftSmoothTriple W) [Flat t] (b : Bool)
    (f : X ⟶ chartScheme W (productChartCoordinate b))
    (hf : f ≫ integralCurveChart W (productChartCoordinate b) =
      t ≫ leftSmoothTripleFirst W ≫ (integralSmoothOpen W).ι) :
    IsRegular (specSectionHom f (coord W (productChartCoordinate b) 2)) :=
  smoothChart_z_regular_of_flat W (t ≫ leftSmoothTripleFirst W) b f hf

/-- The second smooth input has regular Z on every flat Y/Z presentation. -/
theorem leftSmoothTripleSecond_z_regular {X : Scheme.{u}}
    (t : X ⟶ leftSmoothTriple W) [Flat t] (b : Bool)
    (f : X ⟶ chartScheme W (productChartCoordinate b))
    (hf : f ≫ integralCurveChart W (productChartCoordinate b) =
      t ≫ leftSmoothTripleSecond W ≫ (integralSmoothOpen W).ι) :
    IsRegular (specSectionHom f (coord W (productChartCoordinate b) 2)) :=
  smoothChart_z_regular_of_flat W (t ≫ leftSmoothTripleSecond W) b f hf

/-- The arbitrary third input also has regular Z on every flat Y/Z presentation. -/
theorem leftSmoothTripleThird_z_regular {X : Scheme.{u}}
    (t : X ⟶ leftSmoothTriple W) [Flat t] (b : Bool)
    (f : X ⟶ chartScheme W (productChartCoordinate b))
    (hf : f ≫ integralCurveChart W (productChartCoordinate b) =
      t ≫ leftSmoothTripleThird W) :
    IsRegular (specSectionHom f (coord W (productChartCoordinate b) 2)) := by
  have : Flat (f ≫ integralCurveChart W (productChartCoordinate b)) := by
    rw [hf]
    infer_instance
  exact chart_z_regular_of_flat_global W b f

/-- The first sum has regular Z, using only the already proved smooth addition. -/
theorem leftSmoothTripleFirstSum_z_regular {X : Scheme.{u}}
    (t : X ⟶ leftSmoothTriple W) [Flat t] (b : Bool)
    (f : X ⟶ chartScheme W (productChartCoordinate b))
    (hf : f ≫ integralCurveChart W (productChartCoordinate b) =
      t ≫ leftSmoothTriplePair W ≫ smoothFactorAddition W ≫ (integralSmoothOpen W).ι) :
    IsRegular (specSectionHom f (coord W (productChartCoordinate b) 2)) :=
  smoothFactorAddition_z_regular W (t ≫ leftSmoothTriplePair W) b f hf

end FLT.Mazur.WeierstrassIntegralChart
