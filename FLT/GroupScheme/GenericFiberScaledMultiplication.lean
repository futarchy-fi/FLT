/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.GenericFiberMapUnique
public import FLT.GroupScheme.GenericFiberPrimitiveDenominator

/-!
# Multiplication identities for integral numerators

Clearing a generic algebra map by a scalar produces a linear map with scaled
unit and multiplication laws. For a positive uniformizer denominator its
products vanish modulo the uniformizer. This does not prove the Hopf
small-ramification obstruction.
-/

@[expose] public section

open scoped TensorProduct

namespace Algebra

variable {R K A B : Type*} [CommRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  [Module.Flat R B]
  (f : K ⊗[R] A →ₐ[K] K ⊗[R] B) (d : R) (g : A →ₗ[R] B)
  (hg : ∀ x : A, (1 : K) ⊗ₜ[R] g x = d • f ((1 : K) ⊗ₜ[R] x))

include hg

/-- The integral numerator sends one to its clearing scalar. -/
theorem genericFiber_numerator_one : g 1 = algebraMap R B d := by
  apply genericFiber_includeRight_injective (O := R) (K := K)
  change (1 : K) ⊗ₜ[R] g 1 = (1 : K) ⊗ₜ[R] algebraMap R B d
  rw [hg]
  simp only [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    ← Algebra.TensorProduct.one_def, map_one]

/-- Multiplication of two numerator values introduces one extra denominator. -/
theorem genericFiber_numerator_mul (x y : A) : g x * g y = d • g (x * y) := by
  apply genericFiber_includeRight_injective (O := R) (K := K)
  change (1 : K) ⊗ₜ[R] (g x * g y) = (1 : K) ⊗ₜ[R] (d • g (x * y))
  have hm : (1 : K) ⊗ₜ[R] (g x * g y) =
      ((1 : K) ⊗ₜ[R] g x) * ((1 : K) ⊗ₜ[R] g y) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [hm, hg, hg, TensorProduct.tmul_smul, hg]
  rw [smul_mul_smul_comm, ← map_mul]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_smul]

/-- A positive power denominator makes every product of numerator values
divisible by the uniformizer. -/
theorem genericFiber_numerator_mul_dvd_uniformizer (π : R) (n : ℕ)
    (hpow : d = π ^ n) (hn : 0 < n) (x y : A) :
    ∃ z : B, g x * g y = π • z := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  refine ⟨π ^ m • g (x * y), ?_⟩
  rw [genericFiber_numerator_mul f d g hg, hpow, pow_succ', mul_smul]

end Algebra
