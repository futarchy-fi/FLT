/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.ThreeAdicTraceUniverses
public import FLT.GaloisRepresentation.HardlyRamified.CyclotomicTrivialBaseChange

/-! # The actual original three-adic member's characteristic polynomial -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
open scoped TensorProduct
open Polynomial
namespace GaloisRepresentation.IsHardlyRamified
variable {R V : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  [Algebra ℤ_[3] R] [Module.Free ℤ_[3] R] [Module.Finite ℤ_[3] R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[3] R]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
  (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
  (hρ : IsHardlyRamified (⟨1, rfl⟩ : Odd 3) hV ρ)
include hV hρ

/-- The polynomial identity holds on the original module, without a splitting assertion. -/
theorem charpoly_three_universes (g : Field.absoluteGaloisGroup ℚ) :
    (ρ g).charpoly = (X - 1) * (X - C (ρ.det g)) := by
  let b := Module.Free.chooseBasis R V
  have hdim : Module.finrank R V = 2 := Module.finrank_eq_of_rank_eq hV
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex R V) = 2 := by
    simpa only [← Module.finrank_eq_card_chooseBasisIndex] using hdim
  rw [← LinearMap.charpoly_toMatrix (ρ g) b, Matrix.charpoly_of_card_eq_two _ hcard,
    ← LinearMap.trace_eq_matrix_trace R b, LinearMap.det_toMatrix,
    trace_eq_one_add_det_three_universes hV hρ, map_add, map_one]
  change X ^ 2 - (1 + C (ρ.det g)) * X + C (ρ.det g) = _
  ring

/-- All primes distinct from three have the expected original Frobenius polynomial. -/
theorem frobenius_charpoly_three_universes (q : ℕ) (hq : q.Prime) (hq3 : q ≠ 3) :
    (ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat
      (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat)).charpoly =
      (X - 1) * (X - C (q : R)) := by
  change (ρ _).charpoly = _
  rw [charpoly_three_universes hV hρ, hρ.det]
  have h := congrArg (algebraMap ℤ_[3] R)
    (B5Inputs.cyclotomicCharacter_adicArithFrob 3 q hq hq3)
  simp only [map_natCast] at h
  congr 2
  exact congrArg C h

variable (A : Type*) [Field A] [TopologicalSpace A] [IsTopologicalRing A]
  [Algebra R A] [ContinuousSMul R A]

/-- The original member has the common rational polynomial after any coefficient embedding. -/
theorem baseChange_frobenius_three_universes (φ : ℚ →+* A)
    (q : ℕ) (hq : q.Prime) (hq3 : q ≠ 3) :
    ((ρ.baseChange A).toLocal hq.toHeightOneSpectrumRingOfIntegersRat
      (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat)).charpoly =
      (cyclotomicTrivialPolynomial q).map φ := by
  change LinearMap.charpoly ((ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat
    (Field.AbsoluteGaloisGroup.adicArithFrob
      hq.toHeightOneSpectrumRingOfIntegersRat)).baseChange A) = _
  rw [LinearMap.charpoly_baseChange, frobenius_charpoly_three_universes hV hρ q hq hq3]
  simp [cyclotomicTrivialPolynomial]

/-- Framing retains the original member and preserves its Frobenius polynomial. -/
theorem framed_frobenius_three_universes (φ : ℚ →+* A)
    (e : A ⊗[R] V ≃ₗ[A] (Fin 2 → A)) (q : ℕ) (hq : q.Prime) (hq3 : q ≠ 3) :
    (((ρ.baseChange A).conj e).toLocal hq.toHeightOneSpectrumRingOfIntegersRat
      (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat)).charpoly =
      (cyclotomicTrivialPolynomial q).map φ := by
  change (e.conj _).charpoly = _
  rw [LinearEquiv.charpoly_conj]
  exact baseChange_frobenius_three_universes hV hρ A φ q hq hq3

end GaloisRepresentation.IsHardlyRamified
