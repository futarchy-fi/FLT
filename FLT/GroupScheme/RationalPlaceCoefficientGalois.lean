/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceComplexCoefficients
public import FLT.GroupScheme.PDivisibleRationalCartierPeriodGalois
public import FLT.PadicHodgeTheory.ComplexScalarClosed

/-! # The actual coefficient Galois action fixes the original integral base -/

@[expose] public noncomputable section
open PadicHodgeTheory
namespace ThreeAdicPlan
variable {p : ℕ} [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)

/-- Original integral scalars are fixed by every actual complex Galois automorphism. -/
theorem rationalPlaceComplexGalois_base (σ : PadicGalois p) (a : O) :
    complexGalois p σ (algebraMap O ℂ_[p] a) = algebraMap O ℂ_[p] a :=
  complexGalois_algebraMap p σ (rationalPlaceIntegersEquiv p a)

/-- Bundle the actual complex action over the original integral base. -/
def rationalPlaceComplexGalois (σ : PadicGalois p) : ℂ_[p] →ₐ[O] ℂ_[p] :=
  { complexGalois p σ with commutes' := rationalPlaceComplexGalois_base σ }

/-- The actual integral action also fixes the original base. -/
def rationalPlaceIntegerGalois (σ : PadicGalois p) : 𝓞_ℂ_[p] →ₐ[O] 𝓞_ℂ_[p] :=
  { complexIntegerGalois p σ with
    commutes' := fun a ↦ Subtype.ext (rationalPlaceComplexGalois_base σ a) }

/-- Integral coefficient transport retains the original geometric Galois conjugation. -/
theorem rationalPlaceIntegralCoefficients_galois
    (σ : Field.absoluteGaloisGroup ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ))
    (a b : integralClosure O
      (AlgebraicClosure ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)))
    (h : (b : AlgebraicClosure _) = σ a) :
    rationalPlaceIntegerGalois (rationalPlaceGaloisEquiv p σ)
      (rationalPlaceIntegralCoefficients p a) = rationalPlaceIntegralCoefficients p b := by
  apply Subtype.ext
  change complexGalois p (rationalPlaceGaloisEquiv p σ) (rationalPlaceComplexMap p a) =
    rationalPlaceComplexMap p b
  rw [rationalPlaceComplexMap_galois, h]
end ThreeAdicPlan
