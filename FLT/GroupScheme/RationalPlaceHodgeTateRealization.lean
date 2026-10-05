/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceComplexScalarExtension
public import FLT.GroupScheme.RationalPlaceHodgeTateRight

/-! # The full C_p-linear right Hodge–Tate map of the original system -/

@[expose] public noncomputable section
open PadicHodgeTheory
open scoped TensorProduct
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
attribute [local instance 2000] Algebra.toModule Algebra.toSMul
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
variable (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The whole C_p Tate realization, retaining the original integral Tate module. -/
abbrev RationalPlaceTateRealization := ℂ_[p] ⊗[ℤ_[p]] X.tateSequences

/-- Inverting p first gives the same full C_p Tate realization. -/
def rationalPlaceTateRealizationRationalEquiv :
    (ℂ_[p] ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] X.tateSequences)) ≃ₗ[ℂ_[p]]
      RationalPlaceTateRealization X :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ_[p] ℚ_[p] ℂ_[p] ℂ_[p] X.tateSequences

/-- The comparison uses the original integral vector and ordinary scalar multiplication. -/
theorem rationalPlaceTateRealizationRationalEquiv_tmul
    (c : ℂ_[p]) (a : ℚ_[p]) (x : X.tateSequences) :
    rationalPlaceTateRealizationRationalEquiv X (c ⊗ₜ (a ⊗ₜ x)) = (a • c) ⊗ₜ x := rfl

/-- The right Hodge–Tate target is the actual Cartier-dual Lie dual over C_p. -/
abbrev RationalPlaceHodgeTateTarget := ℂ_[p] ⊗[O] Module.Dual O X.cartierDual.IntegralTangent

/-- The right Hodge–Tate map on all C_p Tate vectors. -/
def rationalPlaceHodgeTateRightLinear :
    RationalPlaceTateRealization X →ₗ[ℂ_[p]] RationalPlaceHodgeTateTarget X :=
  rationalPlaceComplexExtend (rationalPlaceHodgeTateRight X)

/-- The full linear map is obtained from the original lattice differential by scalar extension. -/
theorem rationalPlaceHodgeTateRightLinear_tmul (c : ℂ_[p]) (x : X.tateSequences) :
    rationalPlaceHodgeTateRightLinear X (c ⊗ₜ x) =
      c • TensorProduct.comm O _ ℂ_[p] (rationalPlaceHodgeTateRight X x) := rfl

/-- No arbitrary choice of C_p-linear extension changes the original right map. -/
theorem rationalPlaceHodgeTateRightLinear_unique
    (f : RationalPlaceTateRealization X →ₗ[ℂ_[p]] RationalPlaceHodgeTateTarget X)
    (h : ∀ x, f (1 ⊗ₜ x) = TensorProduct.comm O _ ℂ_[p] (rationalPlaceHodgeTateRight X x)) :
    f = rationalPlaceHodgeTateRightLinear X :=
  rationalPlaceComplexExtend_unique _ f h
end ThreeAdicPlan
