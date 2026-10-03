/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.GenericFiberDenominator
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Primitive denominators over a DVR

A generic linear map has a least uniformizer-power denominator. If its exponent
is positive, the integral numerator has a value not divisible by the uniformizer.
The small-ramification Hopf argument ruling out that case remains separate.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra

variable {R K M N : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module.Free R M] [Module.Finite R M]

/-- The common denominator may be chosen as a power of the given uniformizer. -/
theorem genericFiber_exists_pow_denominator {π : R} (hπ : Irreducible π)
    (f : K ⊗[R] M →ₗ[K] K ⊗[R] N) :
    ∃ n : ℕ, ∃ g : M →ₗ[R] N, ∀ x : M,
      (1 : K) ⊗ₜ[R] g x = π ^ n • f ((1 : K) ⊗ₜ[R] x) := by
  obtain ⟨d, hd, g, hg⟩ := genericFiber_exists_denominator f
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hπ
  refine ⟨n, (↑u⁻¹ : R) • g, fun x ↦ ?_⟩
  change (1 : K) ⊗ₜ[R] ((↑u⁻¹ : R) • g x) = _
  rw [TensorProduct.tmul_smul, hg, ← mul_smul, ← mul_assoc, Units.inv_mul, one_mul]

/-- A least denominator has primitive numerator unless its exponent is zero. -/
theorem genericFiber_exists_primitive_denominator {π : R} (hπ : Irreducible π)
    (f : K ⊗[R] M →ₗ[K] K ⊗[R] N) :
    ∃ n : ℕ, ∃ g : M →ₗ[R] N,
      (∀ x : M, (1 : K) ⊗ₜ[R] g x = π ^ n • f ((1 : K) ⊗ₜ[R] x)) ∧
      (n = 0 ∨ ∃ x : M, ¬ ∃ y : N, g x = π • y) := by
  classical
  let P := fun n : ℕ ↦ ∃ g : M →ₗ[R] N, ∀ x : M,
    (1 : K) ⊗ₜ[R] g x = π ^ n • f ((1 : K) ⊗ₜ[R] x)
  have hex : ∃ n, P n := genericFiber_exists_pow_denominator hπ f
  obtain ⟨g, hg⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, g, hg, ?_⟩
  by_cases hn : Nat.find hex = 0
  · exact Or.inl hn
  right
  by_contra! hall
  let b := Module.Free.chooseBasis R M
  choose y hy using fun i ↦ hall (b i)
  let g' : M →ₗ[R] N := b.constr R y
  have heq : g = π • g' := by
    apply b.ext
    intro i
    simpa only [LinearMap.smul_apply, g', Module.Basis.constr_basis] using hy i
  obtain ⟨n, hsucc⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hsmall : P n := by
    refine ⟨g', fun x ↦ ?_⟩
    apply smul_right_injective (M := K ⊗[R] N)
      (show algebraMap R K π ≠ 0 from
        (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hπ.ne_zero)
    simp only [algebraMap_smul]
    have hx := hg x
    rw [heq, LinearMap.smul_apply, TensorProduct.tmul_smul, hsucc, pow_succ', mul_smul] at hx
    exact hx
  exact (Nat.find_min hex (by omega)) hsmall

end Algebra
