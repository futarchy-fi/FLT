/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceThickening
public import FLT.GroupScheme.PDivisibleRationalCartierRoots
public import Mathlib.RingTheory.Valuation.Integral

/-! # Original integral geometric coefficients in the actual O_C -/

@[expose] public noncomputable section
open PadicHodgeTheory
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable (p : ℕ) [Fact p.Prime]

/-- The fixed closure transport agrees with the original integral scalar map. -/
theorem rationalPlaceComplexMap_integralBase
    (x : (LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ) :
    rationalPlaceComplexMap p (algebraMap _ _ x) =
      algebraMap 𝓞_ℂ_[p] ℂ_[p] (algebraMap _ 𝓞_ℂ_[p] x) := by
  change algebraMap (PadicAlgCl p) ℂ_[p]
    (rationalPlaceClosureEquiv p (algebraMap _ _ x)) = _
  rw [IsScalarTower.algebraMap_apply
    ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)
    (AlgebraicClosure ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)),
    rationalPlaceClosureEquiv_algebraMap]
  change algebraMap (PadicAlgCl p) ℂ_[p]
    (algebraMap ℚ_[p] (PadicAlgCl p) (rationalPlaceFieldEquiv p x)) =
      algebraMap ℚ_[p] ℂ_[p] (rationalPlaceIntegersEquiv p x)
  rw [rationalPlaceIntegersEquiv_coe, ← IsScalarTower.algebraMap_apply]

/-- Every original integral geometric coefficient lies in the actual integer ring. -/
theorem rationalPlaceComplexMap_integral
    (x : integralClosure ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      (AlgebraicClosure ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ))) :
    Valued.v (rationalPlaceComplexMap p x) ≤ (1 : NNReal) := by
  apply (PadicComplexInt.integers p).isIntegral_iff_v_le_one.mp
  apply IsIntegral.map_of_comp_eq (algebraMap _ 𝓞_ℂ_[p]) (rationalPlaceComplexMap p) _ x.property
  exact RingHom.ext (fun a ↦ (rationalPlaceComplexMap_integralBase p a).symm)

/-- Integral specialization uses the fixed original closure transport. -/
def rationalPlaceIntegralCoefficients :
    integralClosure ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      (AlgebraicClosure ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)) →ₐ[
        (LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ] 𝓞_ℂ_[p] where
  toFun x := ⟨rationalPlaceComplexMap p x, rationalPlaceComplexMap_integral p x⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  commutes' x := Subtype.ext (rationalPlaceComplexMap_integralBase p x)

/-- Reduction of the specified integral coefficients modulo the actual p-power. -/
def rationalPlaceIntegralModPow (s : ℕ) :
    integralClosure ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      (AlgebraicClosure ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)) →ₐ[
        (LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ] ComplexIntegerModPow p s :=
  (Ideal.Quotient.mkₐ _ _).comp (rationalPlaceIntegralCoefficients p)

end ThreeAdicPlan
