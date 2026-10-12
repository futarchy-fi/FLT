/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFamilyTruncatedRelations
public import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Actual finite free quotient parameters for Hilbert families

The degree truncation has its canonical monomial basis. Evaluation onto a finite
flat family splits by projectivity, and its kernel determines the full family
ideal in degree d+1. Thus the constructed data are actual finite free quotient
parameters over arbitrary rings, before constructing a representing scheme.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.HilbertChart
universe u
variable (S I : Type u) [CommRing S] (J : Ideal (MvPolynomial I S)) (d n : ℕ)

/-- The truncated ambient polynomial module has its canonical bounded monomial basis. -/
def boundedPolynomialBasis : Module.Basis (BoundedHilbertMonomials I n) S
    (MvPolynomial.restrictTotalDegree I S n) :=
  MvPolynomial.basisRestrictSupport S _

/-- The intrinsic relation module inside the bounded ambient free module. -/
def boundedRelationKernel : Submodule S (MvPolynomial.restrictTotalDegree I S n) :=
  LinearMap.ker (boundedQuotientEvaluation S I J n)

/-- Kernel membership is exactly membership in the full original ideal. -/
theorem mem_boundedRelationKernel (p : MvPolynomial.restrictTotalDegree I S n) :
    p ∈ boundedRelationKernel S I J n ↔ p.val ∈ J := by
  change Ideal.Quotient.mk J p.val = 0 ↔ _
  exact Ideal.Quotient.eq_zero_iff_mem

variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
  [Module.Flat S (MvPolynomial I S ⧸ J)]
  (hd : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
    (MvPolynomial I p.asIdeal.ResidueField ⧸
      J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d)

include hd in
/-- Every truncation beyond the uniform degree bound still surjects onto the family. -/
theorem boundedQuotientEvaluation_surjective_of_le (hn : d ≤ n) :
    Function.Surjective (boundedQuotientEvaluation S I J n) := by
  intro x
  obtain ⟨p, hp, hx⟩ := finiteFlat_exists_bounded_representative S I J d hd x
  exact ⟨⟨p, (MvPolynomial.mem_restrictTotalDegree I n p).mpr (hp.trans hn)⟩, hx⟩

include hd in
/-- The constructed bounded quotient has an actual linear section over any coefficient ring. -/
theorem boundedQuotientEvaluation_split (hn : d ≤ n) :
    ∃ s : (MvPolynomial I S ⧸ J) →ₗ[S] MvPolynomial.restrictTotalDegree I S n,
      (boundedQuotientEvaluation S I J n).comp s = LinearMap.id := by
  let _ : Module.Projective S (MvPolynomial I S ⧸ J) :=
    Module.Flat.projective_of_finitePresentation
  exact Module.projective_lifting_property _ LinearMap.id
    (boundedQuotientEvaluation_surjective_of_le S I J d n hd hn)

/-- Quotienting the finite-degree ambient by its actual kernel recovers the original module. -/
def boundedRelationQuotientEquiv (hn : d ≤ n) :
    ((MvPolynomial.restrictTotalDegree I S n) ⧸ boundedRelationKernel S I J n) ≃ₗ[S]
      (MvPolynomial I S ⧸ J) :=
  (boundedQuotientEvaluation S I J n).quotKerEquivOfSurjective
    (boundedQuotientEvaluation_surjective_of_le S I J d n hd hn)

include hd in
/-- The intrinsic kernel in degree d+1 retains all equations of the original family. -/
theorem boundedRelationKernel_generates :
    Ideal.span ((fun p : MvPolynomial.restrictTotalDegree I S (d + 1) ↦ p.val) ''
      (boundedRelationKernel S I J (d + 1) : Set _)) = J := by
  trans truncatedRelationIdeal S I J d
  swap
  · exact finiteFlat_truncatedRelationIdeal_eq S I J d hd
  apply congrArg Ideal.span
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨(mem_boundedRelationKernel S I J (d + 1) q).mp hq,
      (MvPolynomial.mem_restrictTotalDegree I (d + 1) q.val).mp q.property⟩
  · rintro ⟨hJ, hp⟩
    refine ⟨⟨p, (MvPolynomial.mem_restrictTotalDegree I (d + 1) p).mpr hp⟩, ?_, rfl⟩
    exact (mem_boundedRelationKernel S I J (d + 1) _).mpr hJ

end FLT.Mazur.HilbertChart
