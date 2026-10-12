/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveFiberHypotheses
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Connectedness over every field from the original geometric nodal fibers

Extend a field test to its algebraic closure, use the original geometric-fiber
condition, and descend connectedness along the surjective projection.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.FCurve.CurveFiberHypotheses
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X S : Scheme} {f : X ⟶ S}

/-- The geometric nodal-fiber condition implies connectedness on all field tests. -/
theorem NodalGeometricFibers.geometricallyConnected (h : NodalGeometricFibers f) :
    GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ g ↦ ?_⟩
  let a := Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  let q := pullback.snd f g
  have H := (IsPullback.of_hasPullback q a).paste_horiz (IsPullback.of_hasPullback f g)
  let _ : ConnectedSpace (Limits.pullback q a : Scheme) :=
    (h.fiber (AlgebraicClosure K) (a ≫ g) _ _ H).connected
  exact (pullback.fst q a).surjective.connectedSpace (pullback.fst q a).continuous

end FLT.Mazur.FCurve.CurveFiberHypotheses
