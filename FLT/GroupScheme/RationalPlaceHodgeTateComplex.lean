/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceHodgeTateLeftGalois
public import FLT.GroupScheme.RationalPlaceHodgeTateEquivariance
public import FLT.GroupScheme.RationalPlaceTwistSeparation

/-! # The original Hodge–Tate maps form a complex

The vanishing is a consequence of their proved original Galois actions and
nonzero-twist vanishing for C_p. Exactness remains a separate assertion.
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
-- Compare the two original Cartier-dual coefficient structures.
/-- The composite intertwines the original twisted Lie and untwisted dual-Lie actions. -/
theorem rationalPlaceHodgeTateComposite_galois (σ : PadicGalois p)
    (v : RationalPlaceHodgeTateLeftSource X) :
    rationalPlaceHodgeTateRightLinear X
      (rationalPlaceHodgeTateLeft X (rationalPlaceHodgeTateLieTwist X σ v)) =
        rationalPlaceHodgeTateTargetGalois X σ
          (rationalPlaceHodgeTateRightLinear X (rationalPlaceHodgeTateLeft X v)) := by
  rw [rationalPlaceHodgeTateLeft_galois, rationalPlaceHodgeTateRightLinear_padicGalois]

set_option maxHeartbeats 1600000 in
-- Normalize both original maps and the Lie-target scalar structures.
/-- The right map annihilates the left map on every original Lie vector. -/
theorem rationalPlaceHodgeTateRight_left (v : RationalPlaceHodgeTateLeftSource X) :
    rationalPlaceHodgeTateRightLinear X (rationalPlaceHodgeTateLeft X v) = 0 := by
  let := rationalPlace_cotangentLimit_free X.cartierDual
  let : Module.Free O (Module.Dual O X.cartierDual.IntegralTangent) :=
    Module.Free.of_equiv (rationalPlaceCotangentLieDualEquiv X.cartierDual)
  have hone (d : X.IntegralTangent) :
      rationalPlaceHodgeTateRightLinear X
        (rationalPlaceHodgeTateLeft X ((1 : ℂ_[p]) ⊗ₜ[O] d)) = 0 := by
    apply rationalPlaceTensorCyclotomicEigen_eq_zero
    intro σ
    change rationalPlaceHodgeTateTargetGalois X σ _ = _
    rw [← rationalPlaceHodgeTateComposite_galois, rationalPlaceHodgeTateLieTwist_tmul,
      map_one, mul_one]
    have h : rationalPlaceCyclotomicScalar σ ⊗ₜ[O] d =
        rationalPlaceCyclotomicScalar σ • ((1 : ℂ_[p]) ⊗ₜ[O] d) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, (rationalPlaceHodgeTateLeft X).map_smul,
      (rationalPlaceHodgeTateRightLinear X).map_smul]
  induction v using TensorProduct.inductionOn with
  | tmul c d =>
    have h : c ⊗ₜ[O] d = c • ((1 : ℂ_[p]) ⊗ₜ[O] d) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, (rationalPlaceHodgeTateLeft X).map_smul,
      (rationalPlaceHodgeTateRightLinear X).map_smul, hone, smul_zero]
  | add v w hv hw => simp only [map_add, hv, hw, add_zero]

/-- The actual left image lies in the actual right kernel. -/
theorem rationalPlaceHodgeTate_range_le_ker :
    LinearMap.range (rationalPlaceHodgeTateLeft X) ≤
      LinearMap.ker (rationalPlaceHodgeTateRightLinear X) := by
  rintro _ ⟨v, rfl⟩
  exact rationalPlaceHodgeTateRight_left X v
end ThreeAdicPlan
