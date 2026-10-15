/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedCurvePowerIrreducible
public import FLT.Mazur.SmoothGeometricallyReduced
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Geometric integrality of original ordered translation parameters

Smoothness provides geometric reducedness and the ordered-power theorem
provides geometric irreducibility. Consequently every original residue
fiber has the integral coordinate algebras needed by detecting opens.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OrderedCurvePower
variable {X S : Scheme} (f : X ⟶ S) [Smooth f] [GeometricallyIrreducible f]

/-- Every original ordered power is geometrically integral over its unchanged base. -/
theorem base_geometricallyIntegral (n : ℕ) : GeometricallyIntegral (base f n) := by
  let _ := base_smooth f n
  let _ := base_geometricallyIrreducible f n
  let _ := Approximation.geometricallyReduced_of_smooth (base f n)
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _

/-- A specified original fiber retains geometric integrality over its residue field. -/
theorem originalFiber_geometricallyIntegral (n : ℕ) {T Y : Scheme} (t : T ⟶ S)
    {a : Y ⟶ space f n} {b : Y ⟶ T} (H : IsPullback a b (base f n) t) :
    GeometricallyIntegral b := by
  let _ := base_geometricallyIntegral f n
  exact MorphismProperty.of_isPullback H inferInstance

end FLT.Mazur.OrderedCurvePower
