/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Smooth.Flat

/-!
# A lower dimension bound for étale algebras over the affine line

A maximal ideal of a finite type algebra over a Jacobson ring contracts to a
maximal ideal. For a polynomial ring over a field, this contraction strictly
contains the zero ideal. Flat going down lifts this pair to a strict chain
of prime ideals, proving that every nonzero finite type flat algebra has
dimension at least one. In particular this applies to étale algebras.
-/

@[expose] public section

open Polynomial

namespace FLT.Mazur.FCurve

/-- Closed points of a finite type algebra over a Jacobson ring contract to closed points. -/
theorem maximalUnderOfFiniteType
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IsJacobsonRing R] [Algebra.FiniteType R S]
    (M : Ideal S) [M.IsMaximal] : (M.under R).IsMaximal := by
  let := Ideal.Quotient.field M
  have : Module.Finite R (S ⧸ M) := finite_of_finite_type_of_isJacobsonRing R (S ⧸ M)
  have h := Ideal.isMaximal_under_of_isIntegral_of_isMaximal
    (R := R) (⊥ : Ideal (S ⧸ M))
  rw [Ideal.under_def, IsScalarTower.algebraMap_eq R S (S ⧸ M),
    ← Ideal.comap_comap] at h
  simpa [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] using h

/-- Going down produces a strict prime chain below every closed point over the affine line. -/
theorem existsPrimeLtMaximalOfFlatPolynomial
    (K S : Type*) [Field K] [CommRing S] [Algebra K[X] S]
    [Algebra.FiniteType K[X] S] [Module.Flat K[X] S]
    (M : Ideal S) [M.IsMaximal] :
    ∃ P : Ideal S, P < M ∧ P.IsPrime ∧ P.LiesOver (⊥ : Ideal K[X]) := by
  have : (M.under K[X]).IsMaximal := maximalUnderOfFiniteType K[X] S M
  exact Ideal.exists_ideal_lt_liesOver_of_lt M
    (Ideal.bot_lt_of_maximal (M.under K[X]) (Polynomial.not_isField K))

/-- A nonzero finite type flat algebra over the affine line has dimension at least one. -/
theorem oneLeRingKrullDimOfFlatPolynomial
    (K S : Type*) [Field K] [CommRing S] [Nontrivial S] [Algebra K[X] S]
    [Algebra.FiniteType K[X] S] [Module.Flat K[X] S] : 1 ≤ ringKrullDim S := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal S
  obtain ⟨P, hPM, hP, _⟩ := existsPrimeLtMaximalOfFlatPolynomial K S M
  exact Order.one_le_krullDim_iff.mpr ⟨⟨P, hP⟩, ⟨M, inferInstance⟩, hPM⟩

/-- Every nonzero étale algebra over a polynomial ring over a field has dimension at least one. -/
theorem oneLeRingKrullDimOfEtalePolynomial
    (K S : Type*) [Field K] [CommRing S] [Nontrivial S] [Algebra K[X] S]
    [Algebra.Etale K[X] S] : 1 ≤ ringKrullDim S :=
  oneLeRingKrullDimOfFlatPolynomial K S

end FLT.Mazur.FCurve
