/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberAlgebra
public import FLT.Mazur.PolygonSmoothingRing

/-!
# Comparing the two full smoothing-node presentations

The nested polynomial node and the polygon's two-variable quotient have the
same specified product constant. No change of the smoothing parameter is implicit.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.NodalFiber
variable {R : Type*} [CommRing R] (s : R)

/-- Evaluate the full polygon chart at the original two nodal coordinates. -/
def fromSmoothing : PolygonSmoothing.ChartRing s →ₐ[R] Coordinate s :=
  PolygonSmoothing.evaluate s (p s) (q s) (relation s)

/-- Evaluate the original nested polynomial quotient in the full polygon chart. -/
def toSmoothing : Coordinate s →ₐ[R] PolygonSmoothing.ChartRing s :=
  evaluation s (PolygonSmoothing.leftCoordinate s) (PolygonSmoothing.rightCoordinate s)
    (PolygonSmoothing.coordinate_relation s)

@[simp] theorem fromSmoothing_left :
    fromSmoothing s (PolygonSmoothing.leftCoordinate s) = p s :=
  PolygonSmoothing.evaluate_left ..

@[simp] theorem fromSmoothing_right :
    fromSmoothing s (PolygonSmoothing.rightCoordinate s) = q s :=
  PolygonSmoothing.evaluate_right ..

@[simp] theorem toSmoothing_p :
    toSmoothing s (p s) = PolygonSmoothing.leftCoordinate s := evaluation_p ..

@[simp] theorem toSmoothing_q :
    toSmoothing s (q s) = PolygonSmoothing.rightCoordinate s := evaluation_q ..

/-- The full coordinate rings agree while retaining their actual smoothing parameter. -/
def smoothingEquiv : Coordinate s ≃ₐ[R] PolygonSmoothing.ChartRing s :=
  AlgEquiv.ofAlgHom (toSmoothing s) (fromSmoothing s)
    (by apply PolygonSmoothing.chartRing_hom_ext s <;> simp)
    (by apply hom_ext <;> simp)

/-- The first original node generator is the polygon's first coordinate. -/
@[simp] theorem smoothingEquiv_p :
    smoothingEquiv s (p s) = PolygonSmoothing.leftCoordinate s := toSmoothing_p s

/-- The second original node generator is the polygon's second coordinate. -/
@[simp] theorem smoothingEquiv_q :
    smoothingEquiv s (q s) = PolygonSmoothing.rightCoordinate s := toSmoothing_q s

end FLT.Mazur.NodalFiber
