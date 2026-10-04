/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.LocalCyclotomicCharacter
public import FLT.PadicHodgeTheory.AlgebraicClosureGaloisContinuity
public import FLT.PadicHodgeTheory.ComplexGaloisAction

/-! # The original rational-place base and its standard p-adic coordinates -/

@[expose] public noncomputable section
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace ThreeAdicPlan
open PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The original rational completion, identified continuously with Q_p. -/
def rationalPlaceFieldEquiv :
    (LocalCyclotomic.rationalPlace p).adicCompletion ℚ ≃+* ℚ_[p] :=
  (Padic.adicCompletionEquiv (NumberField.RingOfIntegers ℚ)
    ⟨p, Fact.out⟩).symm.toAlgEquiv.toRingEquiv

/-- The original field identification is continuous. -/
theorem rationalPlaceFieldEquiv_continuous : Continuous (rationalPlaceFieldEquiv p) :=
  (Padic.adicCompletionEquiv (NumberField.RingOfIntegers ℚ) ⟨p, Fact.out⟩).symm.continuous

/-- Its actual integer ring, identified continuously with Z_p. -/
def rationalPlaceIntegersEquiv :
    (LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ ≃A[ℤ] ℤ_[p] :=
  (PadicInt.adicCompletionIntegersEquiv (NumberField.RingOfIntegers ℚ) ⟨p, Fact.out⟩).symm

/-- The field and integer identifications commute with their original inclusions. -/
theorem rationalPlaceIntegersEquiv_coe
    (x : (LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ) :
    (rationalPlaceIntegersEquiv p x : ℚ_[p]) = rationalPlaceFieldEquiv p x :=
  PadicInt.coe_adicCompletionIntegersEquiv_symm_apply _ _ x

/-- One fixed closure isomorphism over the actual rational-place field identification. -/
def rationalPlaceClosureEquiv :
    AlgebraicClosure ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) ≃+* PadicAlgCl p :=
  closureFieldTransport (rationalPlaceFieldEquiv p)

/-- The closure identification extends the original base-field map. -/
theorem rationalPlaceClosureEquiv_algebraMap
    (x : (LocalCyclotomic.rationalPlace p).adicCompletion ℚ) :
    rationalPlaceClosureEquiv p (algebraMap _ _ x) =
      algebraMap ℚ_[p] (PadicAlgCl p) (rationalPlaceFieldEquiv p x) :=
  closureFieldTransport_algebraMap _ x

/-- Transport the original local Galois group to the actual group acting on the periods. -/
def rationalPlaceGaloisEquiv :
    Field.absoluteGaloisGroup ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) ≃*
      PadicGalois p :=
  closureGaloisTransport (rationalPlaceFieldEquiv p)

/-- The same original Galois identification is a homeomorphism for the Krull topologies. -/
def rationalPlaceGaloisContinuousEquiv :
    Field.absoluteGaloisGroup ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) ≃ₜ*
      PadicGalois p :=
  closureGaloisContinuousTransport (rationalPlaceFieldEquiv p)

/-- Galois transport and closure transport commute on every original algebraic element. -/
theorem rationalPlaceGaloisEquiv_apply
    (σ : Field.absoluteGaloisGroup ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ))
    (x : AlgebraicClosure ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)) :
    rationalPlaceGaloisEquiv p σ (rationalPlaceClosureEquiv p x) =
      rationalPlaceClosureEquiv p (σ • x) :=
  closureGaloisTransport_apply _ σ x

end ThreeAdicPlan
