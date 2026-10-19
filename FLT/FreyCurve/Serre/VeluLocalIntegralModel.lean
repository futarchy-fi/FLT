/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluSmallRamification

/-!
# Local integral models for actual prime Vélu kernels

A complete discrete valuation ring with sufficiently small absolute ramification
supplies an integral target equation. Away from the kernel prime the bound is
a consequence of that prime being a unit, independent of ramification degree.
-/

@[expose] public section

namespace WeierstrassCurve.Velu

open IsLocalRing

variable {K : Type*} [Field K] [DecidableEq K] [NeZero (2 : K)]
variable (A : ValuationSubring K) (W : WeierstrassCurve A)
variable [IsAdicComplete (maximalIdeal A) A] [IsDiscreteValuationRing A]
variable (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
variable (E : WeierstrassCurve K) (hW : W.map (algebraMap A K) = E)
variable (G : AddSubgroup E.toAffine.Point) [Fintype G]
variable (hG : ∀ Q : G, p • Q.val = 0)

include hp2 hW hG

/-- Local torsion geometry constructs the integral equation of the prescribed Vélu target. -/
theorem exists_prime_kernel_integral_model (hp0 : (p : A) ≠ 0)
    (he : RaynaudParameters.order (p : A) < p - 1) :
    ∃ U : WeierstrassCurve A, U.map (algebraMap A K) = curve E G := by
  subst E
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ :=
    prime_kernel_curve_coefficients_mem A W p hp0 he G hG hp2
  let V := curve (W.map (algebraMap A K)) G
  exact ⟨⟨⟨V.a₁, h₁⟩, ⟨V.a₂, h₂⟩, ⟨V.a₃, h₃⟩, ⟨V.a₄, h₄⟩, ⟨V.a₆, h₆⟩⟩, rfl⟩

/-- Away from the kernel prime the ramification condition is automatic. -/
theorem exists_prime_kernel_integral_model_of_unit (hp : IsUnit (p : A)) :
    ∃ U : WeierstrassCurve A, U.map (algebraMap A K) = curve E G := by
  apply exists_prime_kernel_integral_model A W p hp2 E hW G hG hp.ne_zero
  rw [(RaynaudParameters.order_eq_zero_iff hp.ne_zero).mpr hp]
  exact Nat.sub_pos_of_lt (Nat.Prime.one_lt Fact.out)

end WeierstrassCurve.Velu
