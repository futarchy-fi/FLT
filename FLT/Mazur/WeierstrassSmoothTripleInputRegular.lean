/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothTripleProjections
public import FLT.Mazur.WeierstrassAdditionInputCharts

/-!
# Regular coordinates for the three original smooth triple inputs

Every Y/Z presentation of a flat restriction of an original input has regular
Z coordinate. These statements use only the smooth original projections;
they make no claim about flatness of addition or intermediate sums.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- A Y/Z presentation of any flat map to the smooth curve has regular Z. -/
theorem smoothChart_z_regular_of_flat {X : Scheme.{u}}
    (p : X ⟶ (integralSmoothOpen W).toScheme) [Flat p] (b : Bool)
    (f : X ⟶ chartScheme W (productChartCoordinate b))
    (hf : f ≫ integralCurveChart W (productChartCoordinate b) =
      p ≫ (integralSmoothOpen W).ι) :
    IsRegular (specSectionHom f (coord W (productChartCoordinate b) 2)) := by
  have : Flat (f ≫ integralCurveChart W (productChartCoordinate b)) := by
    rw [hf]
    infer_instance
  exact chart_z_regular_of_flat_global W b f

/-- The first original input has regular Z on every flat chart presentation. -/
theorem smoothTripleFirst_z_regular {X : Scheme.{u}}
    (t : X ⟶ smoothFactorTriple W) [Flat t] (b : Bool)
    (f : X ⟶ chartScheme W (productChartCoordinate b))
    (hf : f ≫ integralCurveChart W (productChartCoordinate b) =
      t ≫ smoothFactorTripleFirst W ≫ (integralSmoothOpen W).ι) :
    IsRegular (specSectionHom f (coord W (productChartCoordinate b) 2)) :=
  smoothChart_z_regular_of_flat W (t ≫ smoothFactorTripleFirst W) b f hf

/-- The middle original input has regular Z on every flat chart presentation. -/
theorem smoothTripleSecond_z_regular {X : Scheme.{u}}
    (t : X ⟶ smoothFactorTriple W) [Flat t] (b : Bool)
    (f : X ⟶ chartScheme W (productChartCoordinate b))
    (hf : f ≫ integralCurveChart W (productChartCoordinate b) =
      t ≫ smoothFactorTripleSecond W ≫ (integralSmoothOpen W).ι) :
    IsRegular (specSectionHom f (coord W (productChartCoordinate b) 2)) :=
  smoothChart_z_regular_of_flat W (t ≫ smoothFactorTripleSecond W) b f hf

/-- The third original input has regular Z on every flat chart presentation. -/
theorem smoothTripleThird_z_regular {X : Scheme.{u}}
    (t : X ⟶ smoothFactorTriple W) [Flat t] (b : Bool)
    (f : X ⟶ chartScheme W (productChartCoordinate b))
    (hf : f ≫ integralCurveChart W (productChartCoordinate b) =
      t ≫ smoothFactorTripleThird W ≫ (integralSmoothOpen W).ι) :
    IsRegular (specSectionHom f (coord W (productChartCoordinate b) 2)) :=
  smoothChart_z_regular_of_flat W (t ≫ smoothFactorTripleThird W) b f hf

end FLT.Mazur.WeierstrassIntegralChart
