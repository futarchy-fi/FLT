/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundedMonomialCover
public import FLT.Mazur.LocalizedKernelComparison
public import Mathlib.RingTheory.LocalProperties.Exactness

/-!
# Bounded polynomial evaluation in arbitrary finite flat families

Degree at most the fiber rank already surjects onto the entire quotient over
any coefficient ring. Surjectivity is checked at maximal localizations using
fiber-dependent bounded monomial bases, without selecting one global basis.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.HilbertChart
universe u
variable (S I : Type u) [CommRing S] (J : Ideal (MvPolynomial I S)) (d : ℕ)

/-- Evaluation of the finite-degree polynomial module in the actual quotient. -/
def boundedQuotientEvaluation :
    MvPolynomial.restrictTotalDegree I S d →ₗ[S] (MvPolynomial I S ⧸ J) :=
  (Ideal.Quotient.mkₐ S J).toLinearMap.comp (MvPolynomial.restrictTotalDegree I S d).subtype

/-- A bounded monomial is an actual vector of the truncated polynomial module. -/
def boundedMonomialPolynomial (m : BoundedHilbertMonomials I d) :
    MvPolynomial.restrictTotalDegree I S d :=
  ⟨MvPolynomial.monomial m.val 1, (MvPolynomial.mem_restrictTotalDegree I d _).mpr
    ((MvPolynomial.totalDegree_monomial_le _ _).trans m.property)⟩

/-- Every bounded basis tuple factors through the single truncated evaluation map. -/
theorem boundedQuotientEvaluation_tuple (m : Fin d → BoundedHilbertMonomials I d) :
    (boundedQuotientEvaluation S I J d).comp
        (tupleLinearMap (fun i ↦ boundedMonomialPolynomial S I d (m i))) =
      tupleLinearMap (polynomialBasisTuple S I d
        (fun i ↦ MvPolynomial.monomial (m i).val 1) S J) := by
  apply (Pi.basisFun S (Fin d)).ext
  intro i
  simp only [LinearMap.comp_apply, tupleLinearMap, Module.Basis.constr_basis,
    boundedQuotientEvaluation, boundedMonomialPolynomial, Submodule.subtype_apply,
    AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, polynomialBasisTuple,
    MvPolynomial.map_monomial, map_one]

variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
  [Module.Flat S (MvPolynomial I S ⧸ J)]
  (hd : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
    (MvPolynomial I p.asIdeal.ResidueField ⧸
      J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d)

include hd in
/-- Bounded evaluation is globally surjective over an arbitrary coefficient ring. -/
theorem boundedQuotientEvaluation_surjective :
    Function.Surjective (boundedQuotientEvaluation S I J d) := by
  apply surjective_of_localized_maximal
  intro P hP
  obtain ⟨m, hm⟩ := exists_boundedMonomial_basisOpen S I S J
    ⟨P, inferInstance⟩ d (hd ⟨P, inferInstance⟩)
  change Function.Bijective (LocalizedModule.map P.primeCompl
    (tupleLinearMap (polynomialBasisTuple S I d
      (fun i ↦ MvPolynomial.monomial (m i).val 1) S J))) at hm
  rw [← boundedQuotientEvaluation_tuple] at hm
  rw [← LocalizedKernelComparison.map_comp] at hm
  exact Function.Surjective.of_comp hm.2

include hd in
/-- Every quotient section admits a representative with the uniform fiber-rank degree bound. -/
theorem finiteFlat_exists_bounded_representative (x : MvPolynomial I S ⧸ J) :
    ∃ p : MvPolynomial I S, p.totalDegree ≤ d ∧ Ideal.Quotient.mk J p = x := by
  obtain ⟨p, hp⟩ := boundedQuotientEvaluation_surjective S I J d hd x
  exact ⟨p.val, (MvPolynomial.mem_restrictTotalDegree I d _).mp p.property, hp⟩

end FLT.Mazur.HilbertChart
