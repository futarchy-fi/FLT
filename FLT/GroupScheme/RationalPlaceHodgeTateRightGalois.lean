/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceHodgeTateDlogGalois
public import FLT.GroupScheme.RationalPlaceHodgeTateRight

/-! # The right lattice differential respects the original Galois action -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open PadicHodgeTheory
open scoped TensorProduct
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
variable (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)
  (σ : Field.absoluteGaloisGroup ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ))

/-- Actual integral bidual evaluation is equivariant on the original Tate module. -/
theorem rationalPlaceCartierBidualTateMap_galois (x : X.tateSequences) :
    X.cartierBidualTateMap (σ • x) = σ • X.cartierBidualTateMap x := by
  apply X.cartierDual.cartierDual.tate_ext
  intro n
  exact map_smul (genericHom ((X.level n).toCartierBidual)) σ (X.tateEval n x)

/-- The right lattice map with cotangent target intertwines the actual original action. -/
theorem rationalPlaceHodgeTateRightCotangent_galois (x : X.tateSequences) :
    (rationalPlaceComplexGalois (rationalPlaceGaloisEquiv p σ)).toLinearMap.lTensor _
      (rationalPlaceHodgeTateRightCotangent X x) =
    rationalPlaceHodgeTateRightCotangent X (σ • x) := by
  change _ = rationalPlaceHodgeTateDlog X.cartierDual (X.cartierBidualTateMap (σ • x))
  rw [rationalPlaceCartierBidualTateMap_galois]
  exact rationalPlaceHodgeTateDlog_galois X.cartierDual σ _

set_option maxHeartbeats 800000 in
-- Elaborating both tensor factors expands the original Cartier-dual Lie module.
/-- The original Lie-dual identification preserves the coefficient Galois action. -/
theorem rationalPlaceHodgeTateRight_galois (x : X.tateSequences) :
    (rationalPlaceComplexGalois (rationalPlaceGaloisEquiv p σ)).toLinearMap.lTensor _
      (rationalPlaceHodgeTateRight X x) = rationalPlaceHodgeTateRight X (σ • x) := by
  have hn (v : X.cartierDual.cotangentLimit ⊗[O] ℂ_[p]) :
      (rationalPlaceComplexGalois (rationalPlaceGaloisEquiv p σ)).toLinearMap.lTensor _
          (TensorProduct.congr (rationalPlaceCotangentLieDualEquiv X.cartierDual)
            (LinearEquiv.refl O ℂ_[p]) v) =
        TensorProduct.congr (rationalPlaceCotangentLieDualEquiv X.cartierDual)
          (LinearEquiv.refl O ℂ_[p])
          ((rationalPlaceComplexGalois (rationalPlaceGaloisEquiv p σ)).toLinearMap.lTensor
            _ v) := by
    induction v using TensorProduct.inductionOn with
    | tmul x c => rfl
    | add v w hv hw => simp only [map_add, hv, hw]
  change _ = TensorProduct.congr (rationalPlaceCotangentLieDualEquiv X.cartierDual)
    (LinearEquiv.refl O ℂ_[p]) (rationalPlaceHodgeTateRightCotangent X (σ • x))
  rw [← rationalPlaceHodgeTateRightCotangent_galois X σ x]
  exact hn _
end ThreeAdicPlan
