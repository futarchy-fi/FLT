/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceHodgeTateRightGalois
public import FLT.GroupScheme.RationalPlaceTateRealizationGalois

/-! # Equivariance of the full original C_p-linear right Hodge–Tate map -/

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

set_option maxHeartbeats 800000 in
-- Definitional comparison expands both the Cartier-dual Lie target and scalar structures.
/-- Swapping tensor factors retains the actual coefficient action on the original right map. -/
theorem rationalPlaceHodgeTateRight_swap_galois
    (σ : Field.absoluteGaloisGroup ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ))
    (x : X.tateSequences) :
    rationalPlaceHodgeTateTargetGalois X (rationalPlaceGaloisEquiv p σ)
      (TensorProduct.comm O _ ℂ_[p] (rationalPlaceHodgeTateRight X x)) =
    TensorProduct.comm O _ ℂ_[p] (rationalPlaceHodgeTateRight X (σ • x)) := by
  have h (v : (Module.Dual O X.cartierDual.IntegralTangent) ⊗[O] ℂ_[p]) :
      rationalPlaceHodgeTateTargetGalois X (rationalPlaceGaloisEquiv p σ)
        (TensorProduct.comm O _ ℂ_[p] v) =
      TensorProduct.comm O _ ℂ_[p]
        ((rationalPlaceComplexGalois (rationalPlaceGaloisEquiv p σ)).toLinearMap.lTensor _ v) := by
    induction v using TensorProduct.inductionOn with
    | tmul d c => rfl
    | add v w hv hw => simp only [map_add, hv, hw]
  exact (h _).trans (congrArg (TensorProduct.comm O _ ℂ_[p])
    (rationalPlaceHodgeTateRight_galois X σ x))

set_option maxHeartbeats 800000 in
-- Tensor induction compares the original lattice and full-realization scalar structures.
/-- The full C_p-linear right map is equivariant for the original diagonal Galois action. -/
theorem rationalPlaceHodgeTateRightLinear_galois
    (σ : Field.absoluteGaloisGroup ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ))
    (v : RationalPlaceTateRealization X) :
    rationalPlaceHodgeTateRightLinear X
        (rationalPlaceTateRealizationGalois X (rationalPlaceGaloisEquiv p σ) v) =
      rationalPlaceHodgeTateTargetGalois X (rationalPlaceGaloisEquiv p σ)
        (rationalPlaceHodgeTateRightLinear X v) := by
  induction v using TensorProduct.inductionOn with
  | tmul c x =>
    change complexGalois p (rationalPlaceGaloisEquiv p σ) c •
        TensorProduct.comm O _ ℂ_[p]
          (rationalPlaceHodgeTateRight X (X.rationalTateAction (rationalPlaceGaloisEquiv p σ) x)) =
      rationalPlaceHodgeTateTargetGalois X (rationalPlaceGaloisEquiv p σ)
        (c • TensorProduct.comm O _ ℂ_[p] (rationalPlaceHodgeTateRight X x))
    have hs := congrArg (fun z : X.tateSequences ↦
      complexGalois p (rationalPlaceGaloisEquiv p σ) c •
        TensorProduct.comm O _ ℂ_[p] (rationalPlaceHodgeTateRight X z))
      (X.rationalTateAction_original σ x)
    exact hs.trans (((rationalPlaceHodgeTateTargetGalois_smul X
      (rationalPlaceGaloisEquiv p σ) c _).trans
        (congrArg (fun z ↦ complexGalois p (rationalPlaceGaloisEquiv p σ) c • z)
          (rationalPlaceHodgeTateRight_swap_galois X σ x))).symm)
  | add v w hv hw => simp only [map_add, hv, hw]

/-- Equivariance also holds in the standard Q_p Galois coordinates. -/
theorem rationalPlaceHodgeTateRightLinear_padicGalois (σ : PadicGalois p)
    (v : RationalPlaceTateRealization X) :
    rationalPlaceHodgeTateRightLinear X (rationalPlaceTateRealizationGalois X σ v) =
      rationalPlaceHodgeTateTargetGalois X σ (rationalPlaceHodgeTateRightLinear X v) := by
  simpa only [MulEquiv.apply_symm_apply] using
    rationalPlaceHodgeTateRightLinear_galois X ((rationalPlaceGaloisEquiv p).symm σ) v
end ThreeAdicPlan
