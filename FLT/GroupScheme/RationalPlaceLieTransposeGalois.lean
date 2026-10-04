/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceHodgeTateLieTwist
public import FLT.GroupScheme.RationalPlaceHodgeTateDlogGalois
public import FLT.GroupScheme.RationalPlaceTateRealizationGalois

/-! # Equivariance of the actual Lie transpose with its positive twist -/

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

/-- Coefficient conjugation on the actual cotangent tensor. -/
def rationalPlaceCotangentGalois (σ : PadicGalois p) :
    ℂ_[p] ⊗[O] X.cotangentLimit →ₗ[O] ℂ_[p] ⊗[O] X.cotangentLimit :=
  (rationalPlaceComplexGalois σ).toLinearMap.rTensor _

set_option maxHeartbeats 800000 in
-- Original bidual scalar structures are compared during the Galois rewrite.
/-- Swapping the original lattice differential commutes with coefficient conjugation. -/
theorem rationalPlaceHodgeTateDlog_swap_galois (σ : PadicGalois p) (y : X.CartierTate) :
    TensorProduct.comm O _ ℂ_[p]
        (rationalPlaceHodgeTateDlog X (X.cartierDual.rationalTateAction σ y)) =
      rationalPlaceCotangentGalois X σ
        (TensorProduct.comm O _ ℂ_[p] (rationalPlaceHodgeTateDlog X y)) := by
  have hy := X.cartierDual.rationalTateAction_original
    ((rationalPlaceGaloisEquiv p).symm σ) y
  simp only [MulEquiv.apply_symm_apply] at hy
  rw [hy, ← rationalPlaceHodgeTateDlog_galois, MulEquiv.apply_symm_apply]
  induction rationalPlaceHodgeTateDlog X y using TensorProduct.inductionOn with
  | tmul d c => rfl
  | add v w hv hw => simp only [map_add, hv, hw]

/-- The full original differential is equivariant on the whole Cartier realization. -/
theorem rationalPlaceHodgeTateDlogLinear_galois (σ : PadicGalois p)
    (y : RationalPlaceTateRealization X.cartierDual) :
    rationalPlaceHodgeTateDlogLinear X (rationalPlaceTateRealizationGalois X.cartierDual σ y) =
      rationalPlaceCotangentGalois X σ (rationalPlaceHodgeTateDlogLinear X y) := by
  have hs (c : ℂ_[p]) (w : ℂ_[p] ⊗[O] X.cotangentLimit) :
      rationalPlaceCotangentGalois X σ (c • w) =
        complexGalois p σ c • rationalPlaceCotangentGalois X σ w := by
    induction w using TensorProduct.inductionOn with
    | tmul b d =>
      change complexGalois p σ (c * b) ⊗ₜ[O] d = _
      rw [map_mul]
      rfl
    | add v w hv hw => simp only [smul_add, map_add, hv, hw]
  induction y using TensorProduct.inductionOn with
  | tmul c y =>
    change complexGalois p σ c • TensorProduct.comm O _ ℂ_[p]
      (rationalPlaceHodgeTateDlog X (X.cartierDual.rationalTateAction σ y)) =
        rationalPlaceCotangentGalois X σ
          (c • TensorProduct.comm O _ ℂ_[p] (rationalPlaceHodgeTateDlog X y))
    rw [hs, rationalPlaceHodgeTateDlog_swap_galois]
  | add v w hv hw => simp only [map_add, hv, hw]

/-- The original Lie evaluation has the same positive cyclotomic covariance as Cartier duality. -/
theorem rationalPlaceLieEvaluation_galois (σ : PadicGalois p)
    (v : RationalPlaceHodgeTateLeftSource X) (w : ℂ_[p] ⊗[O] X.cotangentLimit) :
    rationalPlaceLieEvaluation X (rationalPlaceHodgeTateLieTwist X σ v)
      (rationalPlaceCotangentGalois X σ w) =
        rationalPlaceCyclotomicScalar σ * complexGalois p σ (rationalPlaceLieEvaluation X v w) := by
  induction v using TensorProduct.inductionOn with
  | tmul c d =>
    induction w using TensorProduct.inductionOn with
    | tmul b w =>
      change rationalPlaceLieEvaluation X
        ((rationalPlaceCyclotomicScalar σ * complexGalois p σ c) ⊗ₜ[O] d)
        (complexGalois p σ b ⊗ₜ[O] w) = _
      simp only [rationalPlaceLieEvaluation_tmul, map_mul, rationalPlaceComplexGalois_base]
      ring
    | add v w hv hw => simp only [map_add, hv, hw, mul_add]
  | add v w hv hw => simp only [map_add, LinearMap.add_apply, hv, hw, mul_add]

/-- The transposed original differential intertwines the two original twisted actions. -/
theorem rationalPlaceHodgeTateLieTranspose_galois (σ : PadicGalois p)
    (v : RationalPlaceHodgeTateLeftSource X) (y : RationalPlaceTateRealization X.cartierDual) :
    rationalPlaceHodgeTateLieTranspose X (rationalPlaceHodgeTateLieTwist X σ v)
      (rationalPlaceTateRealizationGalois X.cartierDual σ y) =
        rationalPlaceCyclotomicScalar σ * complexGalois p σ
          (rationalPlaceHodgeTateLieTranspose X v y) := by
  change rationalPlaceLieEvaluation X _ (rationalPlaceHodgeTateDlogLinear X _) = _
  rw [rationalPlaceHodgeTateDlogLinear_galois, rationalPlaceLieEvaluation_galois]
  rfl
end ThreeAdicPlan
