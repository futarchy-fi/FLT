/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatCotangentFinite
public import FLT.GroupScheme.PDivisibleCotangentArithmetic
public import FLT.GroupScheme.PDivisibleRationalPlaceTransport
public import FLT.Mathlib.RingTheory.FiniteTorsionModule

/-! # Finiteness of the original rational-place level cotangent sets -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- Finite p-power residue rings make each original cotangent a finite set. -/
theorem levelCotangent_finite (n : ℕ) [Finite (R ⧸ Ideal.span {(p : R) ^ n})] :
    Finite (X.LevelCotangent n) :=
  Module.finite_of_scalar_annihilator ((p : R) ^ n) (by
    intro a
    simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using X.cotangent_pow_smul_eq_zero n a)

/-- A base identification with Z_p proves actual level-set finiteness without changing models. -/
theorem levelCotangent_finite_of_equiv (e : R ≃+* ℤ_[p]) (n : ℕ) :
    Finite (X.LevelCotangent n) := by
  let := PadicInt.finite_quotient_span_pow_of_equiv p e n
  exact X.levelCotangent_finite n

end ThreeAdicPlan.PDivisibleSystem
namespace ThreeAdicPlan
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
variable {p height : ℕ} [Fact p.Prime]

/-- The original rational-place cotangents themselves, with their original scalars, are finite. -/
theorem rationalPlace_levelCotangent_finite
    (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height) (n : ℕ) :
    Finite (X.LevelCotangent n) := by
  exact X.levelCotangent_finite_of_equiv (rationalPlaceIntegersEquiv p).toRingEquiv n

end ThreeAdicPlan
