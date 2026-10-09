/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupFractionChart
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Homogeneous pieces of the original Rees algebra

The degree n piece consists of the actual polynomials a*T^n with a in I^n.
Multiplication has the expected degree, and coefficient extraction identifies
each homogeneous piece with the corresponding power of the original ideal.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.BlowupRees

variable {A : Type*} [CommRing A] (I : Ideal A)

/-- The original degree n monomial as an element of the actual Rees algebra. -/
def monomialMap (n : ℕ) : ↥(I ^ n) →ₗ[A] reesAlgebra I where
  toFun a := ⟨Polynomial.monomial n (a : A), reesAlgebra.monomial_mem.mpr a.property⟩
  map_add' a b := Subtype.ext (map_add (Polynomial.monomial n) (a : A) (b : A))
  map_smul' a b := Subtype.ext ((Polynomial.monomial n).map_smul a (b : A))

/-- The actual degree n homogeneous submodule of the original Rees algebra. -/
def component (n : ℕ) : Submodule A (reesAlgebra I) := (monomialMap I n).range

/-- Membership is exactly representation by one degree n monomial. -/
theorem mem_component_iff (n : ℕ) (p : reesAlgebra I) :
    p ∈ component I n ↔ ∃ a : ↥(I ^ n), monomialMap I n a = p := Iff.rfl

/-- The defining monomial belongs to its homogeneous component. -/
theorem monomial_mem_component (n : ℕ) (a : ↥(I ^ n)) :
    monomialMap I n a ∈ component I n := ⟨a, rfl⟩

/-- Coefficients recover the ideal element, so the monomial map is injective. -/
theorem monomialMap_injective (n : ℕ) : Function.Injective (monomialMap I n) := by
  intro a b h
  apply Subtype.ext
  have hc := congrArg (fun p : reesAlgebra I => (p : A[X]).coeff n) h
  simpa only [monomialMap, LinearMap.coe_mk, AddHom.coe_mk, coeff_monomial, ite_true] using hc

/-- A homogeneous Rees polynomial has only its degree n coefficient. -/
theorem component_eq_monomial (n : ℕ) (p : reesAlgebra I) (hp : p ∈ component I n) :
    (p : A[X]) = Polynomial.monomial n ((p : A[X]).coeff n) := by
  obtain ⟨a, rfl⟩ := hp
  simp only [monomialMap, LinearMap.coe_mk, AddHom.coe_mk, coeff_monomial, ite_true]

/-- Off-degree coefficients vanish in each homogeneous component. -/
theorem component_coeff_eq_zero {n k : ℕ} (p : reesAlgebra I)
    (hp : p ∈ component I n) (hk : k ≠ n) : (p : A[X]).coeff k = 0 := by
  rw [component_eq_monomial I n p hp]
  simp only [coeff_monomial, Ne.symm hk, ite_false]

/-- Multiplying actual ideal monomials gives their product in the summed degree. -/
theorem monomialMap_mul (n m : ℕ) (a : ↥(I ^ n)) (b : ↥(I ^ m)) :
    monomialMap I n a * monomialMap I m b =
      monomialMap I (n + m) ⟨a * b, by
        rw [pow_add]
        exact Ideal.mul_mem_mul a.property b.property⟩ :=
  Subtype.ext (Polynomial.monomial_mul_monomial n m (a : A) (b : A))

instance component_gradedMonoid : SetLike.GradedMonoid (component I) where
  one_mem := by
    refine ⟨⟨1, by simp⟩, ?_⟩
    apply Subtype.ext
    exact Polynomial.monomial_zero_one
  mul_mem := by
    intro n m p q hp hq
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    rw [monomialMap_mul]
    exact monomial_mem_component I _ _

/-- Each homogeneous component is linearly isomorphic to the original ideal power. -/
def componentEquiv (n : ℕ) : ↥(I ^ n) ≃ₗ[A] component I n :=
  LinearEquiv.ofInjective (monomialMap I n) (monomialMap_injective I n)

end FLT.Mazur.BlowupRees
