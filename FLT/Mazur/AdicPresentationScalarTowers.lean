/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicPresentationDerivation

/-!
# Scalar towers for completed original presentation spaces

The action of the completed presenting ring through its actual projection
agrees with both original presenting coefficients and relative base scalars.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicPresentationScalarTowers

open AdicExtensionProjection

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (P : Algebra.Extension R A) (I : Ideal A)

attribute [local instance] AdicPresentationDerivation.spaceModule

/-- The completed original cotangent space retains its relative base action. -/
theorem targetTower : IsScalarTower R (AdicCompletion I A)
    (AdicCompletion I P.CotangentSpace) :=
  IsScalarTower.of_algebraMap_smul fun r x ↦ by
    rw [IsScalarTower.algebraMap_eq R A (AdicCompletion I A)]
    change algebraMap A (AdicCompletion I A) (algebraMap R A r) • x = r • x
    rw [algebraMap_smul, algebraMap_smul]

/-- The formal projection gives the expected relative action of the presenting completion. -/
theorem relativeTower : IsScalarTower R (AdicCompletion (ideal P I) P.Ring)
    (AdicCompletion I P.CotangentSpace) := by
  let _ := targetTower P I
  exact IsScalarTower.of_algebraMap_smul fun r x ↦ by
    change projection P I (algebraMap R (AdicCompletion (ideal P I) P.Ring) r) • x = r • x
    rw [(projection P I).commutes, algebraMap_smul]

/-- Original presenting scalars agree with their completed action through the projection. -/
theorem originalTower : IsScalarTower P.Ring (AdicCompletion (ideal P I) P.Ring)
    (AdicCompletion I P.CotangentSpace) :=
  IsScalarTower.of_algebraMap_smul fun r x ↦ by
    change projection P I (AdicCompletion.of (ideal P I) P.Ring r) • x = r • x
    rw [projection_of]
    change algebraMap A (AdicCompletion I A) (algebraMap P.Ring A r) • x = r • x
    rw [algebraMap_smul, algebraMap_smul]

end FLT.Mazur.AdicPresentationScalarTowers
