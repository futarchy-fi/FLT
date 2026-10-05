/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceTateScalarDuality

/-! # Full Galois compatibility of the original C_p Cartier pairing -/

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

set_option maxHeartbeats 800000 in
-- Scalar normalization unfolds both tensor factors of the original pairing.
/-- The original root-valued pairing on arbitrary pure tensors retains both coefficients. -/
theorem rationalPlaceTateRootDuality_tmul (c b : ℂ_[p])
    (y : X.CartierTate) (x : X.tateSequences) :
    rationalPlaceTateRootDuality X (c ⊗ₜ y) (b ⊗ₜ x) =
      (c * b) ⊗ₜ X.tateRootDuality y x := by
  have hc : c ⊗ₜ[ℤ_[p]] y = c • ((1 : ℂ_[p]) ⊗ₜ[ℤ_[p]] y) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hb : b ⊗ₜ[ℤ_[p]] x = b • ((1 : ℂ_[p]) ⊗ₜ[ℤ_[p]] x) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hc, hb, (rationalPlaceTateRootDuality X).map_smul]
  rw [LinearMap.smul_apply, map_smul, rationalPlaceTateRootDuality_one_tmul]
  rw [smul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- Full perfect Cartier duality intertwines the original actions on both C_p realizations. -/
theorem rationalPlaceTateRootDuality_galois (σ : PadicGalois p)
    (y : RationalPlaceTateRealization X.cartierDual) (x : RationalPlaceTateRealization X) :
    rationalPlaceTateRootDuality X (rationalPlaceTateRealizationGalois X.cartierDual σ y)
      (rationalPlaceTateRealizationGalois X σ x) =
        rationalPlaceRootGalois p σ (rationalPlaceTateRootDuality X y x) := by
  induction y using TensorProduct.inductionOn with
  | tmul c y =>
    induction x using TensorProduct.inductionOn with
    | tmul b x =>
      simp only [rationalPlaceTateRealizationGalois_tmul, rationalPlaceTateRootDuality_tmul,
        rationalPlaceRootGalois_tmul, map_mul]
      congr 1
      have hx := X.rationalTateAction_original ((rationalPlaceGaloisEquiv p).symm σ) x
      have hy := X.cartierDual.rationalTateAction_original
        ((rationalPlaceGaloisEquiv p).symm σ) y
      simp only [MulEquiv.apply_symm_apply] at hx hy
      rw [hx, hy, X.tateRootDuality_galois]
    | add x z hx hz => simp only [map_add, hx, hz]
  | add y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz]

/-- In cyclotomic coordinates the full pairing acquires exactly the positive character. -/
theorem rationalPlaceTateScalarDuality_galois (σ : PadicGalois p)
    (y : RationalPlaceTateRealization X.cartierDual) (x : RationalPlaceTateRealization X) :
    rationalPlaceTateScalarDuality X (rationalPlaceTateRealizationGalois X.cartierDual σ y)
      (rationalPlaceTateRealizationGalois X σ x) =
        rationalPlaceCyclotomicScalar σ * complexGalois p σ
          (rationalPlaceTateScalarDuality X y x) := by
  simp only [rationalPlaceTateScalarDuality_apply, rationalPlaceTateRootDuality_galois,
    rationalPlaceRootCoordinate_galois]
end ThreeAdicPlan
