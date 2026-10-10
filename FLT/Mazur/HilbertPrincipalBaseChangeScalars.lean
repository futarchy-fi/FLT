/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Scalar extensions between principal localizations

The map from a principal localization to the localization at its image carries
compatible scalar actions over both the source ring and the original base.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.HilbertChart

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (T : Type*) [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
variable (r : S)

/-- The actual localization map induced by a scalar extension. -/
def principalBaseChangeMap :
    Localization.Away r →ₐ[S] Localization.Away (algebraMap S T r) :=
  { __ := IsLocalization.Away.map _ _ (algebraMap S T) r
    commutes' := fun a ↦ by
      change IsLocalization.Away.map _ _ (algebraMap S T) r
        (algebraMap S (Localization.Away r) a) = _
      rw [IsLocalization.Away.map, IsLocalization.map_eq,
        ← IsScalarTower.algebraMap_apply] }

/-- The source localization acts on the principal localization of the new base. -/
@[instance_reducible]
def principalBaseChangeScalars :
    Algebra (Localization.Away r) (Localization.Away (algebraMap S T r)) :=
  (principalBaseChangeMap T r).toRingHom.toAlgebra

/-- The localization map commutes with the original base ring. -/
theorem principalBaseChangeTower :
    let _ := principalBaseChangeScalars T r
    IsScalarTower R (Localization.Away r) (Localization.Away (algebraMap S T r)) := by
  let _ := principalBaseChangeScalars T r
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change algebraMap R _ a = principalBaseChangeMap T r (algebraMap R _ a)
  rw [IsScalarTower.algebraMap_apply R S (Localization.Away r), AlgHom.commutes,
    ← IsScalarTower.algebraMap_apply]

end FLT.Mazur.HilbertChart
