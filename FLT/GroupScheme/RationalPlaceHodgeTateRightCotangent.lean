/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCartierBidualTateEquiv
public import FLT.GroupScheme.RationalPlaceHodgeTateLieTranspose

/-! # The actual right differential in Cartier bidual and cotangent coordinates -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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

/-- Scalar extension of the actual integral bidual equivalence. -/
def rationalPlaceTateBidualEquiv : RationalPlaceTateRealization X ≃ₗ[ℂ_[p]]
    RationalPlaceTateRealization X.cartierDual.cartierDual :=
  X.cartierBidualTateEquiv.baseChange ℤ_[p] ℂ_[p] _ _

/-- The bidual realization retains the original finite-evaluation Tate map. -/
theorem rationalPlaceTateBidualEquiv_tmul (c : ℂ_[p]) (x : X.tateSequences) :
    rationalPlaceTateBidualEquiv X (c ⊗ₜ x) = c ⊗ₜ X.cartierBidualTateMap x := rfl

/-- Cotangent evaluation identifies the original right target after extending scalars. -/
def rationalPlaceHodgeTateTargetEquiv :
    (ℂ_[p] ⊗[O] X.cartierDual.cotangentLimit) ≃ₗ[ℂ_[p]] RationalPlaceHodgeTateTarget X :=
  (rationalPlaceCotangentLieDualEquiv X.cartierDual).baseChange O ℂ_[p] _ _

/-- The target identification is the original evaluation, including on pure tensors. -/
theorem rationalPlaceHodgeTateTargetEquiv_tmul (c : ℂ_[p])
    (v : X.cartierDual.cotangentLimit) :
    rationalPlaceHodgeTateTargetEquiv X (c ⊗ₜ v) =
      c ⊗ₜ rationalPlaceCotangentLieDualEquiv X.cartierDual v := rfl

/-- The target identification commutes with the original coefficient swap. -/
theorem rationalPlaceHodgeTateTargetEquiv_swap
    (z : X.cartierDual.cotangentLimit ⊗[O] ℂ_[p]) :
    rationalPlaceHodgeTateTargetEquiv X (TensorProduct.comm O _ ℂ_[p] z) =
      TensorProduct.comm O _ ℂ_[p]
        (TensorProduct.congr (rationalPlaceCotangentLieDualEquiv X.cartierDual)
          (LinearEquiv.refl O ℂ_[p]) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul v b => rfl
  | add v w hv hw => simp only [map_add, hv, hw]

set_option maxHeartbeats 800000 in
-- Normalize the original semilinear lattice map and its coefficient swap.
/-- The right map is exactly the dual system's differential on actual bidual vectors. -/
theorem rationalPlaceHodgeTateRight_cotangent (x : RationalPlaceTateRealization X) :
    rationalPlaceHodgeTateRightLinear X x = rationalPlaceHodgeTateTargetEquiv X
      (rationalPlaceHodgeTateDlogLinear X.cartierDual (rationalPlaceTateBidualEquiv X x)) := by
  induction x using TensorProduct.inductionOn with
  | tmul c x =>
    change c • TensorProduct.comm O _ ℂ_[p]
        (TensorProduct.congr (rationalPlaceCotangentLieDualEquiv X.cartierDual)
          (LinearEquiv.refl O ℂ_[p])
          (rationalPlaceHodgeTateDlog X.cartierDual (X.cartierBidualTateMap x))) =
      rationalPlaceHodgeTateTargetEquiv X
        (c • TensorProduct.comm O _ ℂ_[p]
          (rationalPlaceHodgeTateDlog X.cartierDual (X.cartierBidualTateMap x)))
    rw [map_smul]
    exact congrArg (fun z ↦ c • z) (rationalPlaceHodgeTateTargetEquiv_swap X _).symm
  | add v w hv hw => simp only [map_add, hv, hw]

/-- Zero in the actual right target is zero of the original dual differential. -/
theorem rationalPlaceHodgeTateRight_eq_zero_iff (x : RationalPlaceTateRealization X) :
    rationalPlaceHodgeTateRightLinear X x = 0 ↔
      rationalPlaceHodgeTateDlogLinear X.cartierDual (rationalPlaceTateBidualEquiv X x) = 0 := by
  rw [rationalPlaceHodgeTateRight_cotangent, (rationalPlaceHodgeTateTargetEquiv X).map_eq_zero_iff]
end ThreeAdicPlan
