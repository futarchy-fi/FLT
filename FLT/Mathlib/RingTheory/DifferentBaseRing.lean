/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.DedekindDomain.Different

/-!
# Changing the presentation of the base integer ring

Two integer rings with the same image in a common fraction field give the
same different ideal in a common integral closure.
-/

@[expose] public noncomputable section

/-- The different only depends on the image of the base integer ring in its
fraction field, not on the chosen presentation of that ring. -/
theorem differentIdeal_eq_of_algebraMap_range_eq
    (A A' K L B : Type*) [CommRing A] [CommRing A'] [Field K] [Field L] [CommRing B]
    [IsDomain A] [IsDomain A'] [IsIntegrallyClosed A] [IsIntegrallyClosed A']
    [Algebra A K] [Algebra A' K] [IsFractionRing A K] [IsFractionRing A' K]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L] [IsDedekindDomain B]
    [Algebra A B] [Algebra A' B] [Algebra A L] [Algebra A' L]
    [IsScalarTower A K L] [IsScalarTower A' K L]
    [IsScalarTower A B L] [IsScalarTower A' B L]
    [IsIntegralClosure B A L] [IsIntegralClosure B A' L]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A' B]
    (h : (algebraMap A K).range = (algebraMap A' K).range) :
    differentIdeal A B = differentIdeal A' B := by
  apply (FractionalIdeal.coeIdeal_inj (K := L)).mp
  rw [coeIdeal_differentIdeal A K L B, coeIdeal_differentIdeal A' K L B]
  congr 1
  apply FractionalIdeal.coeToSubmodule_injective
  dsimp only
  rw [FractionalIdeal.coe_dual_one, FractionalIdeal.coe_dual_one]
  ext x
  simp only [Submodule.mem_traceDual, h]
