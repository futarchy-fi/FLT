/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Full coordinate surjectivity for closed immersions of spectra

The actual preimage under Spec is surjective, without replacing either
coordinate ring by an unspecified isomorphic presentation.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.AffineClosedImmersionCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Closed immersion of the actual spectrum map is full coordinate surjectivity. -/
theorem specMap_iff {R S : CommRingCat} (f : R ⟶ S) :
    IsClosedImmersion (Spec.map f) ↔ Function.Surjective f := by
  rw [HasAffineProperty.iff_of_isAffine (P := @IsClosedImmersion),
    and_iff_right (by infer_instance),
    RingHom.surjective_respectsIso.arrow_mk_iso_iff (arrowIsoΓSpecOfIsAffine f)]

/-- The exact coordinate map of an affine closed immersion is surjective. -/
theorem preimage_surjective {R S : CommRingCat} (f : Spec S ⟶ Spec R)
    [IsClosedImmersion f] : Function.Surjective (Spec.preimage f) := by
  apply (specMap_iff _).mp
  rw [Spec.map_preimage]
  infer_instance

end FLT.Mazur.AffineClosedImmersionCoordinates
