/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceIntegralCoefficients

/-! # Actual C_p coefficients over the original rational-place integers -/

@[expose] public noncomputable section
open PadicHodgeTheory
namespace ThreeAdicPlan
variable (p : ℕ) [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)

/-- Original integral scalars act on C_p through their actual integral coefficient embedding. -/
instance rationalPlaceComplexAlgebra : Algebra O ℂ_[p] :=
  ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (algebraMap O 𝓞_ℂ_[p])).toAlgebra

/-- Integral coefficient inclusion respects the original base action. -/
instance rationalPlaceComplexScalarTower : IsScalarTower O 𝓞_ℂ_[p] ℂ_[p] :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The resulting scalar map is the fixed original closure transport. -/
theorem rationalPlaceComplexAlgebra_algebraMap (x : O) :
    algebraMap O ℂ_[p] x = rationalPlaceComplexMap p (algebraMap _ _ x) :=
  (rationalPlaceComplexMap_integralBase p x).symm
end ThreeAdicPlan
