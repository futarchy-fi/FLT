/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGeometricIntegral
public import FLT.Mazur.WeierstrassIntegralFaithfullyFlat
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Geometric connectedness and components of the actual cubic

Geometric integrality supplies connected fibers. The universally open structure
map therefore identifies the connected components of the cubic with those of
the coefficient spectrum, and this remains true after arbitrary scheme base change.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- All geometric fibers are connected, including singular fibers. -/
instance integralCurveStructure_geometricallyConnected :
    GeometricallyConnected (integralCurveStructure W) := by
  constructor
  intro K _ s Y fst snd h
  let _ := integralCurveFieldSquare_isIntegral W s fst snd h
  infer_instance

/-- The coefficient spectrum and the actual cubic have the same connected components. -/
def integralCurveConnectedComponents :
    ConnectedComponents (integralCurve W) ≃ₜ ConnectedComponents (Spec (.of R)) :=
  (integralCurveStructure W).connectedComponentsHomeomorph
    (integralCurveStructure W).isOpenMap

/-- The actual cubic is connected whenever its coefficient spectrum is connected. -/
theorem integralCurve_connected_of_base [ConnectedSpace (Spec (.of R))] :
    ConnectedSpace (integralCurve W) :=
  GeometricallyConnected.connectedSpace _ (integralCurveStructure W).isOpenMap

variable {S : Scheme.{u}} (f : S ⟶ Spec (.of R))

/-- Connected components are unchanged by the cubic family after arbitrary scheme base change. -/
def integralCurveBaseChangeConnectedComponents :
    ConnectedComponents ↥(pullback (integralCurveStructure W) f) ≃ₜ ConnectedComponents S :=
  (pullback.snd (integralCurveStructure W) f).connectedComponentsHomeomorph
    (pullback.snd (integralCurveStructure W) f).isOpenMap

/-- Any connected base scheme gives a connected pulled-back cubic family. -/
theorem integralCurveBaseChange_connected [ConnectedSpace S] :
    ConnectedSpace ↥(pullback (integralCurveStructure W) f) := inferInstance

/-- Any irreducible base scheme gives an irreducible pulled-back cubic family. -/
theorem integralCurveBaseChange_irreducible [IrreducibleSpace S] :
    IrreducibleSpace ↥(pullback (integralCurveStructure W) f) := inferInstance

end FLT.Mazur.WeierstrassIntegralChart
