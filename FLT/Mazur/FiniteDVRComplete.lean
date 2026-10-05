/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFreeAdicComplete
public import FLT.Mathlib.RingTheory.AdicCompletion.Power
public import FLT.Mathlib.RingTheory.DiscreteValuationRing.TotalRamification
public import Mathlib.RingTheory.Henselian

/-!
# Completeness of finite DVR extensions

A finite faithful DVR algebra over a complete DVR is complete for its own
maximal ideal. The extended base ideal is a positive power of that ideal;
finite free completeness and cofinality of ideal powers give the result.
-/

@[expose] public noncomputable section

namespace FLT.Mazur

open IsLocalRing IsDiscreteValuationRing

variable {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [Module.Finite R S] [FaithfulSMul R S]

/-- The maximal-ideal topology of a finite DVR extension is complete. -/
theorem finiteDVR_isAdicComplete [IsAdicComplete (maximalIdeal R) R] :
    IsAdicComplete (maximalIdeal S) S := by
  obtain ⟨π, hπ⟩ := exists_irreducible R
  obtain ⟨ρ, hρ⟩ := exists_irreducible S
  have hπ0 : algebraMap R S π ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R S)).mpr hπ.ne_zero
  obtain ⟨n, u, hu⟩ := eq_unit_mul_pow_irreducible hπ0 hρ
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    have hi : IsUnit (algebraMap R S π) := by
      rw [hu, hn0, pow_zero, mul_one]
      exact u.isUnit
    exact hπ.not_isUnit (isUnit_of_map_unit (algebraMap R S) π hi)
  have hm : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ^ n := by
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hu,
      Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      ← hρ.maximalIdeal_eq]
  let : IsAdicComplete (maximalIdeal S ^ n) S := by
    rw [← hm]
    exact ThreeAdicPlan.adicComplete_finite_free_algebra (maximalIdeal R) S
  exact IsAdicComplete.ofPow _ hn

/-- A finite DVR extension of a complete DVR satisfies Hensel's lemma. -/
theorem finiteDVR_henselian [IsAdicComplete (maximalIdeal R) R] :
    HenselianLocalRing S := by
  let := finiteDVR_isAdicComplete (R := R) (S := S)
  constructor
  intro f hf x hx hd
  exact HenselianRing.is_henselian f hf x hx (hd.map (residue S))

end FLT.Mazur
