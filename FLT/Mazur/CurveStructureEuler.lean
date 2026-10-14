/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveEulerCharacteristic
public import FLT.Mazur.AffinePushforwardCohomology

/-!
# Structure Euler characteristics and affine direct images

The actual scalar cohomology comparisons preserve h0 minus h1, with the
original structure morphisms retained. A genus-one structure sheaf with
one-dimensional global sections has Euler characteristic zero.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {k : Type} [Field k] {X Y : Scheme}

/-- Structure-module Euler characteristic uses the actual structure-sheaf cohomology. -/
theorem curveEulerCharacteristic_structure (f : X ⟶ Spec (.of k)) :
    curveEulerCharacteristic f (structureUnitModule X) =
      (Module.finrank k (H0 f) : ℤ) - Module.finrank k (H1 f) := by
  unfold curveEulerCharacteristic
  rw [(moduleScalarHUnitEquiv f 0).finrank_eq, (moduleScalarHUnitEquiv f 1).finrank_eq]

/-- One-dimensional H0 and H1 give zero Euler characteristic, also for singular curves. -/
theorem curveEulerCharacteristic_structure_zero (f : X ⟶ Spec (.of k))
    (h0 : Module.finrank k (H0 f) = 1) (h1 : Module.finrank k (H1 f) = 1) :
    curveEulerCharacteristic f (structureUnitModule X) = 0 := by
  rw [curveEulerCharacteristic_structure, h0, h1, sub_self]

/-- Affine direct images preserve Euler characteristic for the original field action. -/
theorem curveEulerCharacteristic_affinePushforward [Y.IsSeparated]
    (f : X ⟶ Y) [IsAffineHom f] (g : Y ⟶ Spec (.of k))
    (M : X.Modules) [M.IsQuasicoherent] :
    curveEulerCharacteristic g ((pushforward f).obj M) =
      curveEulerCharacteristic (f ≫ g) M := by
  unfold curveEulerCharacteristic
  rw [(affinePushforwardScalarHEquiv f M g 0).finrank_eq,
    (affinePushforwardScalarHEquiv f M g 1).finrank_eq]

end FLT.Mazur.FCurve
