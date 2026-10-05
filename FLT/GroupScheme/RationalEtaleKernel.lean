/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalEtaleGenericKernel
public import FLT.GroupScheme.IntegralGenericKernel

/-! # Integral transition-kernel equations of the actual étale quotient tower -/

@[expose] public noncomputable section
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.PDivisibleSystem
variable {p height : ℕ} [Fact p.Prime]
variable (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The original quotient transitions are integrally exact, by flatness and generic exactness. -/
theorem rationalEtale_kernel (m n : ℕ) :
    HopfAlgebra.augmentationIdeal (X.rationalEtaleReduction (Nat.le_add_left n m)) =
      RingHom.ker (X.rationalEtaleInclusion (Nat.le_add_right m n)).toAlgHom.toRingHom :=
  ModelHom.augmentationIdeal_eq_ker_of_generic_exact _ _
    (X.rationalEtaleInclusion_closed _)
    ((X.inclusion _).rationalComponentMap_generic_injective (X.closed _))
    (X.rationalEtaleReduction_faithfullyFlat _).flat (X.rationalEtaleTransition_points_exact m n)
end ThreeAdicPlan.PDivisibleSystem
