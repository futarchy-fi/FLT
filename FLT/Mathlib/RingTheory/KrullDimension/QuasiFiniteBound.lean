/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial

/-! # Dimension bounds for quasi-finite algebras over polynomial rings -/

@[expose] public noncomputable section

/-- Finite fibres imply incomparability of primes, hence a bound on Krull dimension. -/
theorem ringKrullDim_le_of_quasiFinite (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.QuasiFinite R S] : ringKrullDim S ≤ ringKrullDim R := by
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
  intro P Q h
  refine lt_of_le_of_ne (Ideal.comap_mono h.le) ?_
  intro he
  apply h.ne
  exact PrimeSpectrum.ext (Algebra.QuasiFinite.eq_of_le_of_under_eq (R := R)
    P.asIdeal Q.asIdeal
    h.le (congrArg PrimeSpectrum.asIdeal he))

/-- A quasi-finite algebra over affine n-space over a field has dimension at most n. -/
theorem ringKrullDim_le_of_quasiFinite_mvPolynomial (k S : Type*) [Field k] [CommRing S]
    (n : ℕ) [Algebra (MvPolynomial (Fin n) k) S]
    [Algebra.QuasiFinite (MvPolynomial (Fin n) k) S] : ringKrullDim S ≤ n := by
  simpa [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field] using ringKrullDim_le_of_quasiFinite
      (MvPolynomial (Fin n) k) S

end
