/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleRationalCartierRoots
public import FLT.PadicHodgeTheory.ComplexSharpOneLog

/-! # Actual logarithmic period values of the original rational-place Cartier roots

These are period values of pairs of original Tate vectors. Identifying their
infinitesimal terms with the integral cotangent comparison remains a separate obligation.
-/

@[expose] public noncomputable section
open PadicHodgeTheory Finset
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The logarithm of the actual coherent Cartier roots in the existing de Rham period ring. -/
def rationalCartierPeriod (y : X.CartierTate) (x : X.tateSequences) : ComplexBDeRhamPlus p :=
  complexTiltLog p (rationalCartierTilt X y x) (rationalCartierTilt_sharp X y x)

/-- Every finite precision is computed from the same original root sequence. -/
theorem rationalCartierPeriod_truncation (y : X.CartierTate) (x : X.tateSequences) (n : ℕ) :
    rationalCartierPeriod X y x ≡
      (∑ k ∈ range n, complexLogCoefficient p k *
        complexTiltLogArgument p (rationalCartierTilt X y x) ^ k)
      [SMOD ((Ideal.span {complexDeRhamParameter p}) ^ n • ⊤ : Ideal (ComplexBDeRhamPlus p))] :=
  complexTiltLog_truncation p _ _ n

/-- The constructed period value lies in the first filtration ideal. -/
theorem rationalCartierPeriod_mem (y : X.CartierTate) (x : X.tateSequences) :
    rationalCartierPeriod X y x ∈ Ideal.span {complexDeRhamParameter p} :=
  complexTiltLog_mem p _ _

/-- Its first-order term is the Teichmuller difference of the actual Cartier root sequence. -/
theorem rationalCartierPeriod_firstOrder (y : X.CartierTate) (x : X.tateSequences) :
    rationalCartierPeriod X y x - complexTiltLogArgument p (rationalCartierTilt X y x) ∈
      Ideal.span {complexDeRhamParameter p} ^ 2 :=
  complexTiltLog_sub_argument_mem p _ _

/-- Separatedness makes the period independent of any chosen adic summation witness. -/
theorem rationalCartierPeriod_unique (y : X.CartierTate) (x : X.tateSequences)
    (v : ComplexBDeRhamPlus p)
    (hv : ∀ n, (∑ k ∈ range n, complexLogCoefficient p k *
      complexTiltLogArgument p (rationalCartierTilt X y x) ^ k) ≡ v
      [SMOD ((Ideal.span {complexDeRhamParameter p}) ^ n • ⊤ : Ideal (ComplexBDeRhamPlus p))]) :
    rationalCartierPeriod X y x = v :=
  adicSeries_unique _ _ (complexTiltLog_term_mem p _ (rationalCartierTilt_sharp X y x)) v hv

/-- Identical original finite Cartier values produce identical periods. -/
theorem rationalCartierPeriod_ext (y z : X.CartierTate) (x w : X.tateSequences)
    (h : ∀ n, X.cartierTatePairing y x n = X.cartierTatePairing z w n) :
    rationalCartierPeriod X y x = rationalCartierPeriod X z w := by
  have hs : rationalCartierRootSequence X y x = rationalCartierRootSequence X z w := by
    apply Subtype.ext
    funext n
    apply Subtype.ext
    exact congrArg (rationalPlaceComplexMap p) (congrArg Units.val (h n))
  have ht : rationalCartierTilt X y x = rationalCartierTilt X z w :=
    congrArg (Perfection.quotientMulEquiv p (Ideal.span {(p : 𝓞_ℂ_[p])})) hs
  unfold rationalCartierPeriod
  congr 1

end ThreeAdicPlan
