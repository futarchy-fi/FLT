/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXInvolution
public import FLT.Mazur.NodalFiberSmoothingComparison
public import FLT.Mazur.PolygonSmoothingBranchOpens

/-!
# The full incidence map and its reflection symmetry

The pair (t,x) satisfies the smoothing equation on the entire original chart.
This morphism forgets the slope: reflection fixes it. It is not asserted to
be a chart embedding.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
local notation "A" => Coordinate W s b3 b4 b6

/-- The full incidence pair defines a map from the smoothing node algebra. -/
def incidenceNodeMap : NodalFiber.Coordinate s →ₐ[R] A :=
  NodalFiber.evaluation s (t W s b3 b4 b6) (x W s b3 b4 b6)
    (incidence W s b3 b4 b6)

@[simp] theorem incidenceNodeMap_p :
    incidenceNodeMap W s b3 b4 b6 (NodalFiber.p s) = t W s b3 b4 b6 :=
  NodalFiber.evaluation_p ..

@[simp] theorem incidenceNodeMap_q :
    incidenceNodeMap W s b3 b4 b6 (NodalFiber.q s) = x W s b3 b4 b6 :=
  NodalFiber.evaluation_q ..

/-- Reflection loses no incidence information, but cannot be distinguished by this map. -/
theorem incidenceNodeMap_reflection :
    ((initialReflection W s b3 b4 b6).restrictScalars R).toAlgHom.comp
      (incidenceNodeMap W s b3 b4 b6) = incidenceNodeMap W s b3 b4 b6 := by
  apply NodalFiber.hom_ext
  · simp only [AlgHom.comp_apply, incidenceNodeMap_p]
    exact initialReflection_t ..
  · simp only [AlgHom.comp_apply, incidenceNodeMap_q]
    exact initialReflection_x ..

/-- The same incidence map in the full polygon presentation. -/
def incidencePolygonMap : PolygonSmoothing.ChartRing s →ₐ[R] A :=
  (incidenceNodeMap W s b3 b4 b6).comp (NodalFiber.fromSmoothing s)

@[simp] theorem incidencePolygonMap_left :
    incidencePolygonMap W s b3 b4 b6 (PolygonSmoothing.leftCoordinate s) =
      t W s b3 b4 b6 := by
  simp only [incidencePolygonMap, AlgHom.comp_apply, NodalFiber.fromSmoothing_left,
    incidenceNodeMap_p]

@[simp] theorem incidencePolygonMap_right :
    incidencePolygonMap W s b3 b4 b6 (PolygonSmoothing.rightCoordinate s) =
      x W s b3 b4 b6 := by
  simp only [incidencePolygonMap, AlgHom.comp_apply, NodalFiber.fromSmoothing_right,
    incidenceNodeMap_q]

/-- The actual full incidence morphism preserves the original smoothing scale. -/
def incidencePolygonMorphism : Spec (.of A) ⟶ PolygonSmoothing.chart R s :=
  Spec.map (CommRingCat.ofHom (incidencePolygonMap W s b3 b4 b6).toRingHom)

end FLT.Mazur.WeierstrassModificationX
