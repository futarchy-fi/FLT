/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteLeadingIdealFamily
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Unique standard remainders for a monic leading family

Division by actual ideal elements gives a representative supported on the
standard monomials. Leading-monomial control proves uniqueness, including
over nonreduced coefficient rings. The resulting map is a linear equivalence
with the actual ideal quotient, not a newly imposed relation.
-/

@[expose] public noncomputable section
open MvPolynomial
namespace FLT.Mazur.MonicIdealNormalForms
variable {σ R : Type*} [CommRing R] (m : MonomialOrder σ)
  (I : Ideal (MvPolynomial σ R)) (s : Set (MvPolynomial σ R))

/-- Monomials not divisible by any selected leading monomial. -/
def standard : Set (σ →₀ ℕ) := {a | ∀ b ∈ s, ¬ m.degree b ≤ a}

/-- The coefficient module of polynomials supported on standard monomials. -/
def normal : Submodule R (MvPolynomial σ R) :=
  (Finsupp.supported R R (standard m s)).comap
    (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

theorem mem_normal (p : MvPolynomial σ R) : p ∈ normal m s ↔
    ∀ a ∈ p.support, ∀ b ∈ s, ¬ m.degree b ≤ a := Iff.rfl

/-- The map is the restriction of the original quotient map. -/
def quotientMap : normal m s →ₗ[R] MvPolynomial σ R ⧸ I :=
  (Ideal.Quotient.mkₐ R I).toLinearMap.comp (normal m s).subtype

variable (hs : s ⊆ I) (hu : ∀ b ∈ s, IsUnit (m.leadingCoeff b))
  (hc : ∀ p ∈ I, p ≠ 0 → ∃ b ∈ s, m.degree b ≤ m.degree p)

include hs hu in
/-- Division supplies a standard representative in the original ideal class. -/
theorem exists_remainder (p : MvPolynomial σ R) :
    ∃ r : MvPolynomial σ R, r ∈ normal m s ∧ p - r ∈ I := by
  obtain ⟨g, r, hpr, _, hr⟩ := m.div_set hu p
  refine ⟨r, hr, ?_⟩
  rw [hpr, add_sub_cancel_right, Finsupp.linearCombination_apply]
  exact Submodule.sum_mem I fun b _ ↦ I.smul_mem (g b) (hs b.property)

include hc in
/-- A standard polynomial in the original ideal is zero. -/
theorem normal_mem_ideal_eq_zero (p : MvPolynomial σ R)
    (hp : p ∈ normal m s) (hI : p ∈ I) : p = 0 := by
  by_contra hp0
  obtain ⟨b, hb, hbp⟩ := hc p hI hp0
  exact hp (m.degree_mem_support hp0) b hb hbp

include hc in
theorem quotientMap_injective : Function.Injective (quotientMap m I s) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro p hp
  apply (Submodule.mem_bot R).mpr
  apply Subtype.ext
  exact normal_mem_ideal_eq_zero m I s hc p.val p.property
    (Ideal.Quotient.eq_zero_iff_mem.mp hp)

include hs hu in
theorem quotientMap_surjective : Function.Surjective (quotientMap m I s) := by
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨r, hr, hpr⟩ := exists_remainder m I s hs hu p
  exact ⟨⟨r, hr⟩, (Ideal.Quotient.eq.mpr hpr).symm⟩

/-- Unique normal forms are linearly equivalent to the actual ideal quotient. -/
def quotientEquiv : normal m s ≃ₗ[R] MvPolynomial σ R ⧸ I :=
  LinearEquiv.ofBijective (quotientMap m I s)
    ⟨quotientMap_injective m I s hc, quotientMap_surjective m I s hs hu⟩

/-- The equivalence sends a standard polynomial to its unchanged quotient class. -/
theorem quotientEquiv_apply (p : normal m s) :
    quotientEquiv m I s hs hu hc p = Ideal.Quotient.mk I p.val := rfl

/-- Standard coefficients identify the normal module with a genuinely free module. -/
def normalEquiv : normal m s ≃ₗ[R] (standard m s →₀ R) :=
  (AddMonoidAlgebra.coeffLinearEquiv R).ofSubmodule'
      (Finsupp.supported R R (standard m s)) ≪≫ₗ
    Finsupp.supportedEquivFinsupp (standard m s)

/-- A basis indexed by precisely the standard monomials. -/
def quotientBasis : Module.Basis (standard m s) R (MvPolynomial σ R ⧸ I) :=
  Finsupp.basisSingleOne.map
    ((normalEquiv m s).symm.trans (quotientEquiv m I s hs hu hc))

include hs hu hc in
/-- The original quotient is free; no finite rank assertion is made. -/
theorem quotient_free : Module.Free R (MvPolynomial σ R ⧸ I) :=
  Module.Free.of_basis (quotientBasis m I s hs hu hc)

include hs hu hc in
/-- Freeness provides the flatness required for a generic-flatness construction. -/
theorem quotient_flat : Module.Flat R (MvPolynomial σ R ⧸ I) := by
  let _ := quotient_free m I s hs hu hc
  exact Module.Flat.of_free

end FLT.Mazur.MonicIdealNormalForms
