/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleIntegralTangentReduction

/-! # Reduced integral pairings retain the original system maps -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  {X Y : PDivisibleSystem R K p height}

/-- Reducing the integral tangent intertwines the actual level cotangent map. -/
theorem Hom.integralTangentReduction_naturality (f : Hom X Y) (e : R ≃+* ℤ_[p])
    (n : ℕ) (d : X.IntegralTangent) :
    Y.integralTangentReductionEquiv e n (Submodule.Quotient.mk (f.integralTangentMap d)) =
      (X.integralTangentReductionEquiv e n (Submodule.Quotient.mk d)).comp
        (f.app n).cotangentMap := by
  ext a
  obtain ⟨x, rfl⟩ := Y.cotangentEval_surjective n a
  change _ = X.integralTangentReductionEquiv e n (Submodule.Quotient.mk d)
    (X.cotangentEval n (f.cotangentMap x))
  rw [Y.integralTangentReductionEquiv_pairing, X.integralTangentReductionEquiv_pairing]
  rfl

/-- The reduction comparison is independent of the auxiliary identification of the base. -/
theorem integralTangentReductionEquiv_independent (e e' : R ≃+* ℤ_[p]) (n : ℕ) :
    X.integralTangentReductionEquiv e n = X.integralTangentReductionEquiv e' n := by
  ext z a
  obtain ⟨d, rfl⟩ := Submodule.mkQ_surjective _ z
  obtain ⟨x, rfl⟩ := X.cotangentEval_surjective n a
  exact (X.integralTangentReductionEquiv_pairing e n d x).trans
    (X.integralTangentReductionEquiv_pairing e' n d x).symm

end ThreeAdicPlan.PDivisibleSystem
namespace ThreeAdicPlan
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- Original rational-place integral tangent reduction, with no freeness premise. -/
def rationalPlaceIntegralTangentReductionEquiv (n : ℕ) :=
  X.integralTangentReductionEquiv (rationalPlaceIntegersEquiv p).toRingEquiv n

/-- At the original rational place the same integral evaluation is retained modulo p^n. -/
theorem rationalPlaceIntegralTangentReductionEquiv_pairing (n : ℕ)
    (d : X.IntegralTangent) (x : X.cotangentLimit) :
    rationalPlaceIntegralTangentReductionEquiv X n (Submodule.Quotient.mk d)
      (X.cotangentEval n x) = Ideal.Quotient.mk _ (X.integralTangentPairing d x) :=
  X.integralTangentReductionEquiv_pairing (rationalPlaceIntegersEquiv p).toRingEquiv n d x

end ThreeAdicPlan
