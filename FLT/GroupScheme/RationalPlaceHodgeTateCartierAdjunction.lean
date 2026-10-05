/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceHodgeTateRightCotangent
public import FLT.GroupScheme.RationalPlaceHodgeTateComplex
public import FLT.GroupScheme.RationalPlaceLieEvaluationEquiv

/-! # Cartier adjunction and orthogonality for the actual Hodge–Tate maps

The dual-system pairing is evaluated on the original bidual map. No
injectivity, dimension sum, or exactness of the Hodge–Tate sequence is assumed.
-/

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
-- Compare the dual system with its original bidual coefficient structures.
/-- Pairing an actual bidual vector with the dual left map evaluates the right differential. -/
theorem rationalPlaceHodgeTateRight_cartierAdjunction
    (x : RationalPlaceTateRealization X) (w : RationalPlaceHodgeTateLeftSource X.cartierDual) :
    rationalPlaceTateScalarDuality X.cartierDual (rationalPlaceTateBidualEquiv X x)
      (rationalPlaceHodgeTateLeft X.cartierDual w) =
    rationalPlaceLieEvaluation X.cartierDual w
      ((rationalPlaceHodgeTateTargetEquiv X).symm (rationalPlaceHodgeTateRightLinear X x)) := by
  rw [rationalPlaceHodgeTateLeft_pairing, rationalPlaceHodgeTateRight_cotangent,
    LinearEquiv.symm_apply_apply]
  rfl

set_option maxHeartbeats 1600000 in
-- Dual separation unfolds the original two Lie and bidual identifications.
/-- The actual right kernel is the Cartier annihilator of the dual left image. -/
theorem rationalPlaceHodgeTateRight_mem_ker_iff
    (x : RationalPlaceTateRealization X) :
    x ∈ LinearMap.ker (rationalPlaceHodgeTateRightLinear X) ↔
      ∀ w, rationalPlaceTateScalarDuality X.cartierDual (rationalPlaceTateBidualEquiv X x)
        (rationalPlaceHodgeTateLeft X.cartierDual w) = 0 := by
  rw [LinearMap.mem_ker, rationalPlaceHodgeTateRight_eq_zero_iff]
  have he (w : RationalPlaceHodgeTateLeftSource X.cartierDual) :
      rationalPlaceTateScalarDuality X.cartierDual (rationalPlaceTateBidualEquiv X x)
        (rationalPlaceHodgeTateLeft X.cartierDual w) =
      rationalPlaceLieEvaluation X.cartierDual w
        (rationalPlaceHodgeTateDlogLinear X.cartierDual (rationalPlaceTateBidualEquiv X x)) := by
    rw [rationalPlaceHodgeTateLeft_pairing]
    rfl
  simp only [he]
  constructor
  · intro h w
    rw [h, map_zero]
  · intro h
    let : Module.Free ℂ_[p] (ℂ_[p] ⊗[O] X.cartierDual.cotangentLimit) :=
      Module.Free.of_divisionRing _ _
    apply (Module.forall_dual_apply_eq_zero_iff ℂ_[p] _).mp
    intro f
    obtain ⟨w, rfl⟩ := (rationalPlaceLieEvaluationEquiv X.cartierDual).surjective f
    simpa only [← LinearEquiv.coe_toLinearMap, rationalPlaceLieEvaluationEquiv_eq] using h w

set_option maxHeartbeats 800000 in
-- Apply adjunction to the original composite in bidual coordinates.
/-- The two actual Lie images are orthogonal in the dual system's Cartier pairing. -/
theorem rationalPlaceHodgeTateLeft_cartier_orthogonal
    (v : RationalPlaceHodgeTateLeftSource X) (w : RationalPlaceHodgeTateLeftSource X.cartierDual) :
    rationalPlaceTateScalarDuality X.cartierDual
      (rationalPlaceTateBidualEquiv X (rationalPlaceHodgeTateLeft X v))
      (rationalPlaceHodgeTateLeft X.cartierDual w) = 0 := by
  rw [rationalPlaceHodgeTateRight_cartierAdjunction, rationalPlaceHodgeTateRight_left,
    map_zero, map_zero]

/-- Orthogonality holds in the original root-line target, independently of its coordinates. -/
theorem rationalPlaceHodgeTateLeft_root_orthogonal
    (v : RationalPlaceHodgeTateLeftSource X) (w : RationalPlaceHodgeTateLeftSource X.cartierDual) :
    rationalPlaceTateRootDuality X.cartierDual
      (rationalPlaceTateBidualEquiv X (rationalPlaceHodgeTateLeft X v))
      (rationalPlaceHodgeTateLeft X.cartierDual w) = 0 := by
  apply (rationalPlaceRootCoordinate p).injective
  rw [map_zero]
  exact rationalPlaceHodgeTateLeft_cartier_orthogonal X v w
end ThreeAdicPlan
