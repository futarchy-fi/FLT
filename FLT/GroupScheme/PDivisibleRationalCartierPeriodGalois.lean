/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleRationalCartierPeriods

/-! # Original local Galois equivariance of the actual Cartier period values -/

@[expose] public noncomputable section
open PadicHodgeTheory
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)
  (σ : Field.absoluteGaloisGroup ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ))

/-- The fixed original closure transport intertwines the actual complex action. -/
theorem rationalPlaceComplexMap_galois
    (a : AlgebraicClosure ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)) :
    complexGalois p (rationalPlaceGaloisEquiv p σ) (rationalPlaceComplexMap p a) =
      rationalPlaceComplexMap p (σ a) := by
  change complexGalois p (rationalPlaceGaloisEquiv p σ)
    (rationalPlaceClosureEquiv p a : ℂ_[p]) = _
  rw [complexGalois_coe]
  exact congrArg (fun z : PadicAlgCl p ↦ (z : ℂ_[p]))
    (rationalPlaceGaloisEquiv_apply p σ a)

/-- Original simultaneous Galois conjugation acts on the actual integral roots. -/
theorem rationalCartierRoot_galois (y : X.CartierTate) (x : X.tateSequences) (n : ℕ) :
    complexIntegerGalois p (rationalPlaceGaloisEquiv p σ) (rationalCartierRoot X y x n) =
      rationalCartierRoot X (σ • y) (σ • x) n := by
  apply Subtype.ext
  change complexGalois p (rationalPlaceGaloisEquiv p σ)
    (rationalPlaceComplexMap p (X.cartierTatePairing y x n : _)) =
      rationalPlaceComplexMap p (X.cartierTatePairing (σ • y) (σ • x) n : _)
  rw [rationalPlaceComplexMap_galois, X.cartierTatePairing_smul]
  rfl

/-- The complete root sequence, and not only each geometric value, respects Galois. -/
theorem rationalCartierRootSequence_galois (y : X.CartierTate) (x : X.tateSequences) :
    Perfection.mapMonoidHom p (complexIntegerGalois p (rationalPlaceGaloisEquiv p σ)).toMonoidHom
        (rationalCartierRootSequence X y x) =
      rationalCartierRootSequence X (σ • y) (σ • x) := by
  apply Subtype.ext
  funext n
  exact rationalCartierRoot_galois X σ y x n

/-- The original root-to-tilt construction intertwines the same original action. -/
theorem rationalCartierTilt_galois (y : X.CartierTate) (x : X.tateSequences) :
    complexTiltGalois p (rationalPlaceGaloisEquiv p σ) (rationalCartierTilt X y x) =
      rationalCartierTilt X (σ • y) (σ • x) := by
  unfold rationalCartierTilt
  rw [← complexGalois_quotientMulEquiv, rationalCartierRootSequence_galois]

/-- The constructed period values have actual original local Galois equivariance. -/
theorem rationalCartierPeriod_galois (y : X.CartierTate) (x : X.tateSequences) :
    complexDeRhamGalois p (rationalPlaceGaloisEquiv p σ) (rationalCartierPeriod X y x) =
      rationalCartierPeriod X (σ • y) (σ • x) := by
  unfold rationalCartierPeriod
  rw [complexTiltLog_galois]
  congr 1
  exact rationalCartierTilt_galois X σ y x

end ThreeAdicPlan
