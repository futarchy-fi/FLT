/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Flatness from the original local parameter

A Noetherian local domain with principal maximal ideal is Dedekind. Regularity
of its nonzero generator gives torsion-freeness, hence flatness, without any
coefficient-field embedding or change of the original scalar action.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.LocalParameterFlatness

variable (A : Type*) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hgen : IsLocalRing.maximalIdeal A = Ideal.span {π})

include hgen in
/-- A principal maximal ideal makes the original Noetherian local domain Dedekind. -/
theorem isDedekindDomain : IsDedekindDomain A := by
  apply (tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain A).out 5 3 |>.mp
  rw [hgen]
  infer_instance

variable (M : Type*) [AddCommGroup M] [Module A M]
  (hπ : ∀ x : M, π • x = 0 → x = 0)

omit [IsNoetherianRing A] [IsLocalRing A] [IsDomain A] in
include hπ in
/-- Regularity of the original parameter gives regularity of all its powers. -/
theorem pow_smul_eq_zero (d : ℕ) (x : M) (hx : π ^ d • x = 0) : x = 0 := by
  induction d with
  | zero => simpa only [pow_zero, one_smul] using hx
  | succ d ih =>
    rw [pow_succ', mul_smul] at hx
    exact ih (hπ _ hx)

include hgen hπ in
/-- Parameter-regular modules over the original local domain are torsion-free. -/
theorem isTorsionFree (hne : π ≠ 0) : Module.IsTorsionFree A M := by
  let _ : IsPrincipalIdealRing A :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain A).out 5 1).mp (by
      rw [hgen]
      infer_instance)
  let _ : IsDiscreteValuationRing A :=
    { not_a_field' := by
        intro he
        apply hne
        exact Ideal.span_singleton_eq_bot.mp (hgen.symm.trans he) }
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro a x hx
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  obtain ⟨d, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha
    (IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal π hne hgen)
  rw [mul_smul] at hx
  exact pow_smul_eq_zero A π M hπ d x (u.isUnit.smul_eq_zero.mp hx)

include hgen hπ in
/-- Regularity of the original local parameter suffices for flatness. -/
theorem flat (hne : π ≠ 0) : Module.Flat A M := by
  let _ := isDedekindDomain A π hgen
  let _ := isTorsionFree A π hgen M hπ hne
  infer_instance

end FLT.Mazur.LocalParameterFlatness
