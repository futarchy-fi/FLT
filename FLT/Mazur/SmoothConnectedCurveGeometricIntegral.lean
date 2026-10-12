/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothCurveIrreducible
public import FLT.Mazur.SmoothGeometricallyReduced
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Geometric integrality of smooth connected curve families

Connectedness, local domain charts and smooth reducedness prove integrality
on every field test, with no reducedness assumption on the original base.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X S : Scheme} (f : X ⟶ S)
  [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f]

/-- Smooth geometrically connected relative curves are geometrically integral. -/
theorem smoothConnectedCurve_geometricallyIntegral : GeometricallyIntegral f := by
  refine ⟨fun K _ g P p q H ↦ ?_⟩
  let _ : SmoothOfRelativeDimension 1 q :=
    MorphismProperty.of_isPullback H inferInstance
  let _ := SmoothOfRelativeDimension.smooth 1 q
  let _ : ConnectedSpace P :=
    GeometricallyConnected.geometrically_connectedSpace g p q H
  let _ := smoothCurve_irreducible q
  let _ := Approximation.isReduced_of_smooth_field q
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end FLT.Mazur.FCurve
