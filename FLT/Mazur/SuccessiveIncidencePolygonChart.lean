/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SuccessiveIncidenceAlgebra
public import FLT.Mazur.PolygonSmoothingRing
public import FLT.Mazur.WeierstrassSuccessiveXMonicComparison

/-!
# The original incidence base is the polygon node chart

The two presentations of t*u = π are identified over the unchanged coefficient
ring. The successive Weierstrass chart maps to this node chart by its actual
incidence coordinates; its slope still satisfies the original quadratic.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.SuccessiveIncidence
open PolygonSmoothing
variable {R : Type*} [CommRing R] (π : R)

/-- The actual incidence algebra evaluates in the original polygon node ring. -/
def toPolygon : Coordinate π →ₐ[R] ChartRing π :=
  evaluation π (leftCoordinate π) (rightCoordinate π) (coordinate_relation π)

/-- The node ring evaluates in the incidence algebra without changing π. -/
def fromPolygon : ChartRing π →ₐ[R] Coordinate π :=
  evaluate π (t π) (u π) (incidence π)

/-- The first incidence coordinate is the first polygon branch coordinate. -/
@[simp] theorem toPolygon_t : toPolygon π (t π) = leftCoordinate π := evaluation_t ..

/-- The retained horizontal coordinate is the second polygon branch coordinate. -/
@[simp] theorem toPolygon_u : toPolygon π (u π) = rightCoordinate π := evaluation_u ..

/-- The reverse comparison retains the first coordinate. -/
@[simp] theorem fromPolygon_left : fromPolygon π (leftCoordinate π) = t π := evaluate_left ..

/-- The reverse comparison retains the second coordinate. -/
@[simp] theorem fromPolygon_right : fromPolygon π (rightCoordinate π) = u π := evaluate_right ..

/-- The actual original node algebras are inverse over their original coefficients. -/
def polygonEquiv : Coordinate π ≃ₐ[R] ChartRing π :=
  AlgEquiv.ofAlgHom (toPolygon π) (fromPolygon π) (by
    apply chartRing_hom_ext <;> simp only [AlgHom.comp_apply, fromPolygon_left,
      fromPolygon_right, toPolygon_t, toPolygon_u, AlgHom.id_apply]) (by
    apply hom_ext <;> simp only [AlgHom.comp_apply, fromPolygon_left,
      fromPolygon_right, toPolygon_t, toPolygon_u, AlgHom.id_apply])

end FLT.Mazur.SuccessiveIncidence

namespace FLT.Mazur.WeierstrassSuccessiveX
open PolygonSmoothing
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)

/-- The original successive chart receives the original polygon node coordinates. -/
def polygonNodeMap : ChartRing π →ₐ[R] Coordinate W s π b3 b4 b6 :=
  (incidenceToCoordinate W s π b3 b4 b6).comp (SuccessiveIncidence.fromPolygon π)

/-- The first node coordinate is exactly the incidence ratio. -/
@[simp] theorem polygonNodeMap_left :
    polygonNodeMap W s π b3 b4 b6 (leftCoordinate π) = coord W s π b3 b4 b6 0 := by
  simp only [polygonNodeMap, AlgHom.comp_apply, SuccessiveIncidence.fromPolygon_left,
    incidenceToCoordinate, SuccessiveIncidence.evaluation_t]

/-- The second node coordinate is the retained horizontal coordinate. -/
@[simp] theorem polygonNodeMap_right :
    polygonNodeMap W s π b3 b4 b6 (rightCoordinate π) = coord W s π b3 b4 b6 2 := by
  simp only [polygonNodeMap, AlgHom.comp_apply, SuccessiveIncidence.fromPolygon_right,
    incidenceToCoordinate, SuccessiveIncidence.evaluation_u]

end FLT.Mazur.WeierstrassSuccessiveX
