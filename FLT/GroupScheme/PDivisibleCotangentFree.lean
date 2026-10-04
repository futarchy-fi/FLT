/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCotangentPrimeInjective
public import FLT.GroupScheme.PDivisibleCotangentLimitFinite
public import FLT.GroupScheme.PDivisibleCotangentFiniteSets
public import Mathlib.LinearAlgebra.FreeModule.PID

/-! # Torsion-freeness and finite freeness of the original cotangent limit -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- The original cotangent limit is torsion-free over a base identified with Z_p. -/
theorem cotangentLimit_isTorsionFree (e : R ≃+* ℤ_[p]) :
    Module.IsTorsionFree R X.cotangentLimit := by
  let (n : ℕ) : Finite (X.LevelCotangent n) := X.levelCotangent_finite_of_equiv e n
  let : IsDiscreteValuationRing R := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    e.symm
  have hp : Irreducible (p : R) := by
    rw [← MulEquiv.irreducible_iff (f := e), map_natCast]
    exact PadicInt.irreducible_p
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro a x hx
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hp
  have hpow : (p : R) ^ n • x = 0 := by
    apply u.isUnit.smul_left_cancel.mp
    simpa only [mul_smul, smul_zero] using hx
  clear hx ha u
  induction n with
  | zero => simpa using hpow
  | succ n ih =>
    apply ih
    apply X.cotangentLimit_eq_zero_of_prime_smul hp.ne_zero
    simpa only [pow_succ', mul_smul] using hpow

/-- Finite generation and proved torsion-freeness give freeness of the same integral limit. -/
theorem cotangentLimit_free (e : R ≃+* ℤ_[p]) : Module.Free R X.cotangentLimit := by
  let : IsPrincipalIdealRing R := IsPrincipalIdealRing.of_surjective e.symm e.symm.surjective
  let : Module.Finite R X.cotangentLimit := X.cotangentLimit_finite e
  let : Module.IsTorsionFree R X.cotangentLimit := X.cotangentLimit_isTorsionFree e
  infer_instance

end ThreeAdicPlan.PDivisibleSystem
namespace ThreeAdicPlan
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- Torsion-freeness for the original rational-place cotangent inverse limit. -/
theorem rationalPlace_cotangentLimit_isTorsionFree :
    Module.IsTorsionFree ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      X.cotangentLimit :=
  X.cotangentLimit_isTorsionFree (rationalPlaceIntegersEquiv p).toRingEquiv

/-- Freeness for the original rational-place limit; its finite generation was proved earlier. -/
theorem rationalPlace_cotangentLimit_free :
    Module.Free ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ) X.cotangentLimit :=
  X.cotangentLimit_free (rationalPlaceIntegersEquiv p).toRingEquiv

end ThreeAdicPlan
