/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineScaledEndpointReversal

/-!
# Reversing a scaled reciprocal parameter

Reversing the orientation of a complete projective component replaces its
reciprocal constant c by c inverse. Both full affine charts prove the formula.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (K : Type u) [Field K]

/-- Exchanging complete affine charts inverts the projective scaling unit. -/
@[reassoc] theorem scaling_endpointReversal (c : Kˣ) :
    scaling K c ≫ endpointReversal K = endpointReversal K ≫ scaling K c⁻¹ := by
  apply pushout.hom_ext
  · change left K ≫ _ = left K ≫ _
    rw [left_scaling_assoc, left_endpointReversal, left_endpointReversal_assoc,
      right_scaling, inv_inv]
  · change right K ≫ _ = right K ≫ _
    rw [right_scaling_assoc, right_endpointReversal, right_endpointReversal_assoc,
      left_scaling]

/-- Reversing the domain orientation keeps the full reciprocal with the inverse constant. -/
@[reassoc] theorem endpointReversal_scaledEndpointReversal (c : Kˣ) :
    endpointReversal K ≫ scaledEndpointReversal K c =
      scaledEndpointReversal K c⁻¹ ≫ endpointReversal K := by
  simp only [scaledEndpointReversal, Category.assoc, scaling_endpointReversal,
    inv_inv]

end FLT.Mazur.ProjectiveLine
