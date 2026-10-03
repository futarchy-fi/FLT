/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Endpoint interpolation for bounded polynomials

Constant and highest allowed coefficients model the two endpoint values of a
homogeneous polynomial on the projective line. The explicit right inverse
works over any commutative ring. No identification with sheaf sections is made.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.PolynomialEndpointInterpolation
variable {R : Type*} [CommRing R]

/-- Polynomials of degree at most d+1, with d+1 strictly positive. -/
abbrev Bounded (R : Type*) [CommRing R] (d : ℕ) := degreeLT R (d + 2)

/-- The constant and highest allowed coefficients. -/
def endpoints (d : ℕ) : Bounded R d →ₗ[R] R × R where
  toFun p := (p.val.coeff 0, p.val.coeff (d + 1))
  map_add' p q := by ext <;> simp
  map_smul' a p := by ext <;> simp

/-- A linear right inverse to endpoint restriction. -/
def interpolate (d : ℕ) : (R × R) →ₗ[R] Bounded R d where
  toFun v := ⟨monomial 0 v.1 + monomial (d + 1) v.2,
    (degreeLT R (d + 2)).add_mem
      (monomial_coe_mem_degreeLT ⟨0, by omega⟩ _)
      (monomial_coe_mem_degreeLT ⟨d + 1, by omega⟩ _)⟩
  map_add' v w := by apply Subtype.ext; simp [map_add]; abel
  map_smul' a v := by apply Subtype.ext; simp [smul_add, smul_monomial]

/-- The interpolating polynomial in ordinary polynomial notation. -/
@[simp] theorem interpolate_val (d : ℕ) (a b : R) :
    (interpolate d (a, b)).val = C a + monomial (d + 1) b := rfl

/-- Both prescribed endpoint values are recovered. -/
@[simp] theorem endpoints_interpolate (d : ℕ) (v : R × R) :
    endpoints d (interpolate d v) = v := by
  ext <;> simp [endpoints, interpolate, coeff_monomial]

/-- Endpoint restriction is surjective over every commutative ring. -/
theorem endpoints_surjective (d : ℕ) : Function.Surjective (endpoints (R := R) d) :=
  fun v ↦ ⟨interpolate d v, endpoints_interpolate d v⟩

/-- The first endpoint is evaluation at zero. -/
@[simp] theorem endpoints_fst (d : ℕ) (p : Bounded R d) :
    (endpoints d p).1 = p.val.eval 0 := by simp [endpoints, coeff_zero_eq_eval_zero]

/-- The bounded polynomial space has the expected dimension. -/
theorem finrank_bounded (K : Type*) [Field K] (d : ℕ) :
    Module.finrank K (Bounded K d) = d + 2 := by
  rw [(degreeLTEquiv K (d + 2)).finrank_eq]
  simp
end FLT.Mazur.PolynomialEndpointInterpolation
