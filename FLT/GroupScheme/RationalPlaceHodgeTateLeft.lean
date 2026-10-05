/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceTateScalarDuality

/-! # The actual left Hodge–Tate map into the original Tate realization -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open PadicHodgeTheory
open scoped TensorProduct
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
attribute [local instance 2000] Algebra.toModule Algebra.toSMul
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
variable (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- Transport the original Lie transpose through perfect Cartier duality. -/
def rationalPlaceHodgeTateLeft : RationalPlaceHodgeTateLeftSource X →ₗ[ℂ_[p]]
    RationalPlaceTateRealization X :=
  (rationalPlaceTateLeftDuality X).symm.toLinearMap.comp (rationalPlaceHodgeTateLieTranspose X)

/-- The actual left map is characterized by the original Lie-Cartier differential pairing. -/
theorem rationalPlaceHodgeTateLeft_pairing (v : RationalPlaceHodgeTateLeftSource X)
    (y : RationalPlaceTateRealization X.cartierDual) :
    rationalPlaceTateScalarDuality X y (rationalPlaceHodgeTateLeft X v) =
      rationalPlaceHodgeTateLieTranspose X v y := by
  change rationalPlaceTateLeftDuality X
    ((rationalPlaceTateLeftDuality X).symm (rationalPlaceHodgeTateLieTranspose X v)) y = _
  rw [LinearEquiv.apply_symm_apply]

/-- The defining pairing determines the original Tate vector uniquely. -/
theorem rationalPlaceHodgeTateLeft_unique (v : RationalPlaceHodgeTateLeftSource X)
    (x : RationalPlaceTateRealization X)
    (h : ∀ y, rationalPlaceTateScalarDuality X y x = rationalPlaceHodgeTateLieTranspose X v y) :
    x = rationalPlaceHodgeTateLeft X v := by
  apply rationalPlaceTateScalarDuality_separates X
  intro y
  rw [h, rationalPlaceHodgeTateLeft_pairing]

/-- Perfect duality introduces no additional kernel in the actual left map. -/
theorem rationalPlaceHodgeTateLeft_ker :
    LinearMap.ker (rationalPlaceHodgeTateLeft X) =
      LinearMap.ker (rationalPlaceHodgeTateLieTranspose X) := by
  ext v
  simp only [LinearMap.mem_ker]
  change (rationalPlaceTateLeftDuality X).symm (rationalPlaceHodgeTateLieTranspose X v) = 0 ↔ _
  exact (rationalPlaceTateLeftDuality X).symm.map_eq_zero_iff
end ThreeAdicPlan
