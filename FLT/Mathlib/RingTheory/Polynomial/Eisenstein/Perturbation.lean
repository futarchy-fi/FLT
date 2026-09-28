/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Monomial perturbations of Eisenstein polynomials

Subtracting a lower-degree monomial preserves the Eisenstein condition when
its coefficient belongs to the prime ideal, and to its square if the
monomial is constant. The resulting simple field extension has the original
degree and an integral generator with a prescribed polynomial value.
-/

@[expose] public noncomputable section

universe u

open Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R] {P : R[X]} {I : Ideal R} {a : R} {s : ℕ}

/-- Subtracting a lower-degree monomial does not change the degree. -/
theorem natDegreeSubMonomial (hs : s < P.natDegree) :
    (P - monomial s a).natDegree = P.natDegree :=
  natDegree_sub_eq_left_of_natDegree_lt ((natDegree_monomial_le a).trans_lt hs)

/-- Subtracting a lower-degree monomial preserves monicity. -/
theorem Monic.subMonomial (hP : P.Monic) (hs : s < P.natDegree) :
    (P - monomial s a).Monic := by
  change (P - monomial s a).leadingCoeff = 1
  rw [leadingCoeff_sub_of_degree_lt
    (degree_lt_degree ((natDegree_monomial_le a).trans_lt hs))]
  exact hP

/-- An Eisenstein polynomial remains Eisenstein after a sufficiently divisible
lower-degree monomial is subtracted. -/
theorem IsEisensteinAt.subMonomial (hP : P.IsEisensteinAt I)
    (hs : s < P.natDegree) (ha : a ∈ I) (ha0 : s = 0 → a ∈ I ^ 2) :
    (P - monomial s a).IsEisensteinAt I := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rw [leadingCoeff_sub_of_degree_lt
      (degree_lt_degree ((natDegree_monomial_le a).trans_lt hs))]
    exact hP.leading
  · intro i hi
    rw [natDegreeSubMonomial hs] at hi
    rw [coeff_sub, coeff_monomial]
    exact I.sub_mem (hP.mem hi) (by split_ifs <;> simp_all)
  · rw [coeff_sub, coeff_monomial]
    by_cases hs0 : s = 0
    · simp only [hs0, ite_true]
      intro h
      exact hP.notMem (sub_add_cancel (P.coeff 0) a ▸ (I ^ 2).add_mem h (ha0 hs0))
    · simpa [hs0] using hP.notMem

/-- A root of the perturbed polynomial realizes the removed monomial as the
value of the original polynomial. -/
theorem aevalEqOfSubMonomialRoot {S : Type*} [CommRing S] [Algebra R S]
    (y : S) (hy : aeval y (P - monomial s a) = 0) :
    aeval y P = algebraMap R S a * y ^ s := by
  simpa only [map_sub, aeval_monomial, sub_eq_zero, Algebra.smul_def] using hy

/-- The Eisenstein monomial perturbation is irreducible over the fraction field. -/
theorem IsEisensteinAt.irreducibleMapSubMonomial [IsDomain R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (hP : P.IsEisensteinAt I) (hPm : P.Monic) (hI : I.IsPrime)
    (hs : s < P.natDegree) (ha : a ∈ I) (ha0 : s = 0 → a ∈ I ^ 2) :
    Irreducible ((P - monomial s a).map (algebraMap R K)) := by
  apply (hPm.subMonomial hs).irreducible_iff_irreducible_map_fraction_map.mp
  apply (hP.subMonomial hs ha ha0).irreducible hI (hPm.subMonomial hs).isPrimitive
  rw [natDegreeSubMonomial hs]
  exact Nat.zero_le s |>.trans_lt hs

/-- A monic Eisenstein perturbation has an integral root in a field extension
of the original polynomial degree, with the required exact polynomial identity. -/
theorem IsEisensteinAt.existsPerturbedExtension
    {R K : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {P : R[X]} {I : Ideal R} {a : R} {s : ℕ}
    (hP : P.IsEisensteinAt I) (hPm : P.Monic) (hI : I.IsPrime)
    (hs : s < P.natDegree) (ha : a ∈ I) (ha0 : s = 0 → a ∈ I ^ 2) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : FiniteDimensional K E)
      (_ : Algebra R E) (_ : IsScalarTower R K E) (y : E),
      IsIntegral R y ∧ Module.finrank K E = P.natDegree ∧
        aeval y P = algebraMap R E a * y ^ s := by
  let Q := P - monomial s a
  have hQ : Q.Monic := hPm.subMonomial hs
  let q := Q.map (algebraMap R K)
  let instIrreducible : Fact (Irreducible q) :=
    ⟨hP.irreducibleMapSubMonomial K hPm hI hs ha ha0⟩
  let E := AdjoinRoot q
  let instFinite : FiniteDimensional K E :=
    (AdjoinRoot.powerBasis (hQ.map (algebraMap R K)).ne_zero).finite
  have hy : aeval (AdjoinRoot.root q) Q = 0 := by
    rw [AdjoinRoot.aeval_eq_of_algebra]
    exact AdjoinRoot.mk_self
  refine ⟨E, inferInstance, inferInstance, instFinite, inferInstance, inferInstance,
    AdjoinRoot.root q, ⟨Q, hQ, hy⟩, ?_, aevalEqOfSubMonomialRoot _ hy⟩
  rw [(AdjoinRoot.powerBasis (hQ.map (algebraMap R K)).ne_zero).finrank]
  change q.natDegree = P.natDegree
  rw [hQ.natDegree_map, natDegreeSubMonomial hs]

end Polynomial
