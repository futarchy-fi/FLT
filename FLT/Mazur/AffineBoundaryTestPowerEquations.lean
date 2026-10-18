/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBoundaryTestThickenings

/-!
# Exact power equations for the full scalar test product

The affine ideal correspondence preserves powers. Thus an original test
neighborhood is the entire product as a scheme exactly when its power is zero.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryProduct boundaryCoordinate
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T) (a : Finset B)

/-- The actual sheaf and coordinate ideals have identical zero-power equations. -/
theorem boundaryTestSheaf_pow_eq_bot_iff (k : ℕ) :
    boundaryTestSheaf s κ a ^ k = ⊥ ↔ boundaryTestIdeal s κ a ^ k = ⊥ := by
  let E := Scheme.IdealSheafData.equivOfIsAffine (X := boundaryProduct s κ)
  have h : E (boundaryTestSheaf s κ a) = boundaryTestIdeal s κ a := by
    exact E.apply_symm_apply _
  rw [← E.injective.eq_iff, map_pow]
  change E (boundaryTestSheaf s κ a) ^ k = E ⊥ ↔ _
  rw [h, map_bot]

/-- A finite test order recovers the full product iff its actual power vanishes. -/
theorem boundaryTestThickeningMap_isIso_iff (k : ℕ) :
    IsIso (boundaryTestThickeningMap s κ a k) ↔ boundaryTestIdeal s κ a ^ (k + 1) = ⊥ := by
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot, boundaryTestThickeningMap_kernel,
    boundaryTestSheaf_pow_eq_bot_iff]

end FLT.Mazur.AffineScalarBoundaryNilpotence
