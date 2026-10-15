/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Coordinate units on morphisms contained in a principal open

Containment in the actual principal open makes the pulled-back coordinate
invertible. Functions killed by that coordinate vanish after pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OpenRangeCoordinateUnit
universe u
variable {U X : Scheme.{u}} (f : U ⟶ X)

/-- A coordinate is a unit on any scheme whose image lies in its principal open. -/
theorem isUnit_appTop (a : Γ(X, ⊤))
    (ha : Set.range f ⊆ (X.basicOpen a : Set X)) : IsUnit (f.appTop a) := by
  apply U.toRingedSpace.isUnit_of_isUnit_germ
  intro z hz
  apply (Scheme.mem_basicOpen U (f.appTop a) z hz).mp
  rw [← Scheme.preimage_basicOpen_top]
  exact ha ⟨z, rfl⟩

/-- Every coordinate-annihilated section is zero on schemes contained in its principal open. -/
theorem appTop_eq_zero (a z : Γ(X, ⊤))
    (ha : Set.range f ⊆ (X.basicOpen a : Set X)) (hz : a * z = 0) : f.appTop z = 0 := by
  apply (isUnit_appTop f a ha).mul_left_cancel
  rw [mul_zero, ← map_mul, hz, map_zero]

end FLT.Mazur.OpenRangeCoordinateUnit
