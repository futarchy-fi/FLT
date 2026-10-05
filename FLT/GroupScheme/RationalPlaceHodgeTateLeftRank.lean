/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceHodgeTateLeftImage

/-! # Dimensions of the actual left Hodge–Tate kernel and image

The formulas retain the rank of the original differential. Determining that
rank for the connected system is the remaining comparison theorem.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
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

set_option maxHeartbeats 800000 in
-- Compare ranges through both original scalar-extended equivalences.
/-- The image dimension of the actual left map is exactly the rank of the Cartier differential. -/
theorem rationalPlaceHodgeTateLeft_range_finrank :
    Module.finrank ℂ_[p] (LinearMap.range (rationalPlaceHodgeTateLeft X)) =
      Module.finrank ℂ_[p] (LinearMap.range (rationalPlaceHodgeTateDlogLinear X)) := by
  rw [rationalPlaceHodgeTateLeft_factorization, LinearMap.range_comp,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
    LinearEquiv.finrank_map_eq, LinearMap.finrank_range_dualMap_eq_finrank_range]

/-- The actual left source has the dimension of the original integral cotangent limit. -/
theorem rationalPlaceHodgeTateLeftSource_finrank :
    Module.finrank ℂ_[p] (RationalPlaceHodgeTateLeftSource X) =
      Module.finrank O X.cotangentLimit := by
  let := rationalPlace_cotangentLimit_free X
  rw [(rationalPlaceLieEvaluationEquiv X).finrank_eq, Subspace.dual_finrank_eq,
    Module.finrank_baseChange]

/-- The original left source is finite dimensional, as proved by perfect Lie evaluation. -/
theorem rationalPlace_hodgeTateLeftSource_finite :
    Module.Finite ℂ_[p] (RationalPlaceHodgeTateLeftSource X) := by
  let := rationalPlace_cotangentRealization_finite X
  exact Module.Finite.equiv (rationalPlaceLieEvaluationEquiv X).symm

/-- The unresolved kernel dimension is the precise defect of the original differential rank. -/
theorem rationalPlaceHodgeTateLeft_kernel_dimension :
    Module.finrank ℂ_[p] (LinearMap.range (rationalPlaceHodgeTateDlogLinear X)) +
      Module.finrank ℂ_[p] (LinearMap.ker (rationalPlaceHodgeTateLeft X)) =
        Module.finrank O X.cotangentLimit := by
  let := rationalPlace_hodgeTateLeftSource_finite X
  rw [← rationalPlaceHodgeTateLeft_range_finrank,
    LinearMap.finrank_range_add_finrank_ker, rationalPlaceHodgeTateLeftSource_finrank]
end ThreeAdicPlan
