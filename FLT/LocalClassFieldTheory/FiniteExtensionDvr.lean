/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteExtensionLocalRing
public import FLT.LocalClassFieldTheory.FiniteDvrComplete
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Canonical DVRs in finite extensions

Spectral-norm locality, Dedekindness, and nonfieldness prove that the canonical
integral closure is a DVR. No local-ring or valuation-extension premise is added.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

variable (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [IsAdicComplete (maximalIdeal R) R]

include K in
/-- The canonical integral closure in every finite separable extension is a DVR. -/
theorem finiteExtension_dvr : IsDiscreteValuationRing (integralClosure R L) := by
  let : IsLocalRing (integralClosure R L) := finiteExtension_integralClosure_local R K L
  let : IsDedekindDomain (integralClosure R L) :=
    IsIntegralClosure.isDedekindDomain R K L (integralClosure R L)
  let : Module.IsTorsionFree R L := .trans_faithfulSMul R K L
  have hn : ¬ IsField (integralClosure R L) := fun h =>
    IsDiscreteValuationRing.not_isField R
      (isField_of_isIntegral_of_isField (FaithfulSMul.algebraMap_injective R _) h)
  exact ((IsDiscreteValuationRing.TFAE (integralClosure R L) hn).out 3 1).mp
    (inferInstance : IsDedekindDomain (integralClosure R L))

end LocalClassFieldTheory
