/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.PowerBasisDifferentials
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.Localization.Module

/-!
# The different of a monogenic integral closure

The conductor formula for the trace-dual different and the power-basis
calculation of Kähler differentials identify the different with the
annihilator of the differentials when the integral closure has a power basis.
-/

@[expose] public noncomputable section

open Polynomial

namespace PowerBasis

variable {A B : Type*} (K L : Type*) [CommRing A] [IsDomain A]
  [Field K] [CommRing B] [Field L] [Algebra A K] [Algebra A B]
  [Algebra B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [IsScalarTower A B L] [IsFractionRing A K] [FiniteDimensional K L]
  [IsIntegralClosure B A L]

/-- An integral power-basis generator also generates the fraction-field extension. -/
theorem adjoin_fractionField_gen_eq_top (pb : PowerBasis A B) :
    Algebra.adjoin K {algebraMap B L pb.gen} = ⊤ := by
  let := IsIntegralClosure.isLocalization A K L B
  have hspan := span_eq_top_localization_localization K (nonZeroDivisors A) L pb.basis.span_eq
  apply top_unique
  intro y _
  have hy : y ∈ Submodule.span K (algebraMap B L '' Set.range pb.basis) := by
    rw [hspan]
    trivial
  apply (show Submodule.span K (algebraMap B L '' Set.range pb.basis) ≤
    (Algebra.adjoin K {algebraMap B L pb.gen}).toSubmodule from ?_) hy
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  rw [pb.basis_eq_pow, map_pow]
  exact (Algebra.adjoin K {algebraMap B L pb.gen}).pow_mem
    (Algebra.subset_adjoin (Set.mem_singleton _)) _

variable [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
  [Algebra.IsSeparable K L]

include K L

/-- The different of a monogenic integral closure is its minimal-polynomial derivative ideal. -/
theorem differentIdeal_eq_span_minpoly_derivative (pb : PowerBasis A B) :
    differentIdeal A B = Ideal.span {aeval pb.gen (derivative (minpoly A pb.gen))} := by
  simpa [conductor_eq_top_of_powerBasis pb] using
    conductor_mul_differentIdeal A K L pb.gen (pb.adjoin_fractionField_gen_eq_top K L)

/-- For a monogenic integral closure, the trace-dual different equals the
annihilator of the Kähler differentials. -/
theorem differentIdeal_eq_annihilator_kaehlerDifferential (pb : PowerBasis A B) :
    differentIdeal A B = Module.annihilator B (KaehlerDifferential A B) := by
  rw [pb.differentIdeal_eq_span_minpoly_derivative K L, pb.annihilator_kaehlerDifferential]

/-- Differential annihilation is equivalent to membership in the different
for a monogenic integral closure. -/
theorem mem_differentIdeal_iff (pb : PowerBasis A B) (b : B) :
    b ∈ differentIdeal A B ↔ ∀ ω : KaehlerDifferential A B, b • ω = 0 := by
  rw [pb.differentIdeal_eq_annihilator_kaehlerDifferential K L, Module.mem_annihilator]

end PowerBasis
