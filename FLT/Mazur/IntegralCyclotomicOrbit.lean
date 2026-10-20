/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegralCyclotomicCoordinates
public import FLT.Mazur.RootsOfUnityLaurentKernel
public import FLT.Mazur.LaurentUnitKernel

/-!
# The integral cyclotomic orbit equation and all its specializations

All powers of the integral cyclotomic coordinate factor the full roots-of-unity
polynomial. Mapping this identity to an arbitrary ring preserves the product,
even when several powers coincide in residue characteristic dividing the order.
-/

@[expose] public noncomputable section

open Polynomial LaurentPolynomial
open scoped LaurentPolynomial

namespace FLT.Mazur.IntegralCyclotomicOrbit

open IntegralCyclotomicCoordinates

variable (n : ℕ) [NeZero n]

/-- Integrally, the orbit of a cyclotomic coordinate factors the entire root polynomial. -/
theorem polynomial : (X : (Coordinate n)[X]) ^ n - 1 =
    ∏ i : Fin n, (X - Polynomial.C (root n ^ i.val)) := by
  classical
  rw [X_pow_sub_one_eq_prod (NeZero.pos n) (primitive n)]
  symm
  refine Finset.prod_bij (fun i _ ↦ root n ^ i.val) ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro i _
    apply (mem_nthRootsFinset (NeZero.pos n) (1 : Coordinate n)).mpr
    rw [← pow_mul, Nat.mul_comm, pow_mul, root_pow, one_pow]
  · intro i _ j _ hij
    exact Fin.ext ((primitive n).pow_inj i.isLt j.isLt hij)
  · intro a ha
    obtain ⟨i, hi, he⟩ := (primitive n).eq_pow_of_pow_eq_one
      ((mem_nthRootsFinset (NeZero.pos n) (1 : Coordinate n)).mp ha)
    exact ⟨⟨i, hi⟩, Finset.mem_univ _, he⟩

/-- The full orbit equation survives every specialization, without a distinctness hypothesis. -/
theorem polynomial_specialization {R : Type*} [CommRing R] (φ : Coordinate n →+* R) :
    (X : R[X]) ^ n - 1 = ∏ i : Fin n, (X - Polynomial.C (φ (root n) ^ i.val)) := by
  simpa only [Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one,
    Polynomial.map_prod, map_C, map_pow] using congrArg (Polynomial.map φ) (polynomial n)

/-- The orbit equation on the torus retains all special-fiber multiplicities. -/
theorem laurent_specialization {R : Type*} [CommRing R] (φ : Coordinate n →+* R) :
    T (n : ℤ) - (1 : R[T;T⁻¹]) =
      ∏ i : Fin n, (T 1 - LaurentPolynomial.C (φ (root n) ^ i.val)) := by
  simpa only [map_sub, Polynomial.toLaurent_X_pow, map_one, map_prod,
    Polynomial.toLaurent_X, Polynomial.toLaurent_C] using
    congrArg Polynomial.toLaurent (polynomial_specialization n φ)

/-- The actual subgroup kernel is the product of the specialized orbit's principal ideals. -/
theorem kernel_specialization {R : Type*} [CommRing R] (φ : Coordinate n →+* R) :
    RingHom.ker (RootsOfUnityAlgebra.restriction R n).toAlgHom.toRingHom =
      ∏ i : Fin n, Ideal.span {T 1 - LaurentPolynomial.C (φ (root n) ^ i.val)} := by
  rw [RootsOfUnityLaurentKernel.kernel, laurent_specialization n φ]
  exact (Ideal.prod_span_singleton _ _).symm

/-- The orbit factors are the full ideals of the actual specialized unit points. -/
theorem kernel_unit_orbit {R : Type*} [CommRing R] (φ : Coordinate n →+* R) :
    RingHom.ker (RootsOfUnityAlgebra.restriction R n).toAlgHom.toRingHom =
      ∏ i : Fin n, RingHom.ker (LaurentUnitPoints.evalUnit (R := R)
        ((Units.map φ.toMonoidHom (rootUnit n)) ^ i.val)).toRingHom := by
  rw [kernel_specialization n φ]
  apply Finset.prod_congr rfl
  intro i _
  rw [LaurentUnitKernel.kernel]
  rfl

end FLT.Mazur.IntegralCyclotomicOrbit
