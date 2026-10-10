/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Scalar structures on a common principal neighborhood

Inverting both factors gives the actual scalar extensions from each principal
localization. The scalar tower identities are proved from the localization maps.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.HilbertChart

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (r s : S)

/-- The actual map from the first principal localization to the product localization. -/
def principalProductLeftMap : Localization.Away r →ₐ[S] Localization.Away (r * s) where
  __ := IsLocalization.Away.awayToAwayRight r s
  commutes' := IsLocalization.Away.awayToAwayRight_eq r s

/-- The actual map from the second principal localization to the product localization. -/
def principalProductRightMap : Localization.Away s →ₐ[S] Localization.Away (r * s) where
  __ := IsLocalization.Away.awayToAwayLeft s r
  commutes' := IsLocalization.Away.awayToAwayLeft_eq s r

/-- The left localization acts on the actual common principal localization. -/
@[instance_reducible]
def principalProductLeftScalars : Algebra (Localization.Away r) (Localization.Away (r * s)) :=
  (principalProductLeftMap r s).toRingHom.toAlgebra

/-- The right localization acts on the actual common principal localization. -/
@[instance_reducible]
def principalProductRightScalars : Algebra (Localization.Away s) (Localization.Away (r * s)) :=
  (principalProductRightMap r s).toRingHom.toAlgebra

/-- The first scalar action respects every original base algebra. -/
theorem principalProductLeftTower :
    let _ := principalProductLeftScalars r s
    IsScalarTower R (Localization.Away r) (Localization.Away (r * s)) := by
  let _ := principalProductLeftScalars r s
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change algebraMap R _ a = principalProductLeftMap r s (algebraMap R _ a)
  rw [IsScalarTower.algebraMap_apply R S (Localization.Away r), AlgHom.commutes,
    ← IsScalarTower.algebraMap_apply]

/-- The second scalar action respects every original base algebra. -/
theorem principalProductRightTower :
    let _ := principalProductRightScalars r s
    IsScalarTower R (Localization.Away s) (Localization.Away (r * s)) := by
  let _ := principalProductRightScalars r s
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change algebraMap R _ a = principalProductRightMap r s (algebraMap R _ a)
  rw [IsScalarTower.algebraMap_apply R S (Localization.Away s), AlgHom.commutes,
    ← IsScalarTower.algebraMap_apply]

end FLT.Mazur.HilbertChart
