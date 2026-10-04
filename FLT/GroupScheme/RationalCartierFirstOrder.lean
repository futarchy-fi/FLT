/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceIntegralCoefficients
public import FLT.GroupScheme.PDivisibleCartierDlogLimit
public import FLT.PadicHodgeTheory.ComplexThickeningRootPower

/-! # The original finite Cartier root and its first-order Teichmuller value -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open PadicHodgeTheory HopfAlgebra.CartierDual
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The integral Cartier pairing specializes to the specified original root in O_C. -/
theorem rationalCartierRoot_integralPairing (y : X.CartierTate) (x : X.tateSequences) (n : ℕ) :
    rationalPlaceIntegralCoefficients p
      ((X.level n).integralCartierPairing (X.cartierTateEval n y) (X.tateEval n x)) =
        rationalCartierRoot X y x n := by
  apply Subtype.ext
  change rationalPlaceComplexMap p _ = rationalPlaceComplexMap p _
  exact congrArg (rationalPlaceComplexMap p) ((X.level n).integralCartierPairing_coe _ _)

/-- Finite test-algebra evaluation is the reduction of that same original root. -/
theorem rationalCartierRoot_modPow (y : X.CartierTate) (x : X.tateSequences) (s n : ℕ) :
    (testCharacter ((rationalPlaceIntegralModPow p s).comp (X.cartierTateIntegralCoordinate n y))
      (WithConv.toConv ((rationalPlaceIntegralModPow p s).comp
        ((X.level n).integralPointCoordinate (X.tateEval n x)))) : ComplexIntegerModPow p s) =
      Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ s}) (rationalCartierRoot X y x n) := by
  rw [testCharacter_coe, AlgHom.comp_toLinearMap, ← testEvaluation_coefficients]
  change rationalPlaceIntegralModPow p s
    ((X.level n).integralCartierPairing (X.cartierTateEval n y) (X.tateEval n x)) = _
  change Ideal.Quotient.mk _ (rationalPlaceIntegralCoefficients p _) = _
  rw [rationalCartierRoot_integralPairing]

/-- The original Teichmuller difference in the actual first-order integral coefficient ring. -/
def rationalCartierFirstOrder (s : ℕ) (y : X.CartierTate) (x : X.tateSequences) :
    RingHom.ker (rationalPlaceThickeningTheta p 2 s (by decide)) :=
  ⟨Ideal.Quotient.mk (complexThickeningIdeal p 2 s)
      (WittVector.teichmuller p (rationalCartierTilt X y x) - 1), by
    change Ideal.Quotient.mk _ (complexTheta p
      (WittVector.teichmuller p (rationalCartierTilt X y x) - 1)) = 0
    rw [map_sub, complexTheta_teichmuller, rationalCartierTilt_sharp,
      map_one, sub_self, map_zero]⟩

/-- Any lift of the original level-s Cartier value computes this Teichmuller difference. -/
theorem rationalCartierFirstOrder_eq_root_lift (s : ℕ) (y : X.CartierTate) (x : X.tateSequences)
    (a : ComplexIntegralThickening p 2 s)
    (ha : complexThickeningTheta p 2 s (by decide) a =
      Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ s}) (rationalCartierRoot X y x s)) :
    (rationalCartierFirstOrder X s y x : ComplexIntegralThickening p 2 s) = a ^ (p ^ s) - 1 := by
  have h := complexThickening_root_lift_pow p s (rationalCartierRootSequence X y x) a ha
  have ht : complexRootSequenceShift p (rationalCartierRootSequence X y x) 0 =
      rationalCartierTilt X y x := by
    rfl
  rw [ht] at h
  change Ideal.Quotient.mk _ (WittVector.teichmuller p (rationalCartierTilt X y x) - 1) = _
  rw [map_sub, map_one, ← h]

end ThreeAdicPlan
