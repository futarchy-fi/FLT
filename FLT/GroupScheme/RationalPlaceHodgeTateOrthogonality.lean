/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceHodgeTateComplex

/-! # The actual two Lie images are orthogonal in the original Cartier pairing

The proof uses the positive cyclotomic actions on both left maps and the
positive cyclotomic target of Cartier duality. It assumes no comparison rank.
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

/-- The original integral Lie vectors map to cyclotomic eigenvectors. -/
theorem rationalPlaceHodgeTateLeft_one_galois (σ : PadicGalois p) (d : X.IntegralTangent) :
    rationalPlaceTateRealizationGalois X σ (rationalPlaceHodgeTateLeft X (1 ⊗ₜ[O] d)) =
      rationalPlaceCyclotomicScalar σ • rationalPlaceHodgeTateLeft X (1 ⊗ₜ[O] d) := by
  rw [← rationalPlaceHodgeTateLeft_galois, rationalPlaceHodgeTateLieTwist_tmul,
    map_one, mul_one]
  have he : rationalPlaceCyclotomicScalar σ ⊗ₜ[O] d =
      rationalPlaceCyclotomicScalar σ • ((1 : ℂ_[p]) ⊗ₜ[O] d) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [he, map_smul]

set_option maxHeartbeats 800000 in
-- Both original Cartier factors carry their own dual-system action.
/-- Pairing original integral Lie images yields zero, by nonzero-twist vanishing. -/
theorem rationalPlaceHodgeTateLeft_pairing_one_eq_zero
    (d : X.IntegralTangent) (e : X.cartierDual.IntegralTangent) :
    rationalPlaceTateScalarDuality X (rationalPlaceHodgeTateLeft X.cartierDual (1 ⊗ₜ[O] e))
      (rationalPlaceHodgeTateLeft X (1 ⊗ₜ[O] d)) = 0 := by
  apply rationalPlaceCyclotomicEigen_eq_zero
  intro σ
  have hn : rationalPlaceCyclotomicScalar σ ≠ 0 :=
    ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).isUnit.map
      (algebraMap ℤ_[p] ℂ_[p])).ne_zero
  have h := rationalPlaceTateScalarDuality_galois X σ
    (rationalPlaceHodgeTateLeft X.cartierDual (1 ⊗ₜ[O] e))
    (rationalPlaceHodgeTateLeft X (1 ⊗ₜ[O] d))
  rw [rationalPlaceHodgeTateLeft_one_galois, rationalPlaceHodgeTateLeft_one_galois] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  exact (mul_left_cancel₀ hn h).symm

set_option maxHeartbeats 800000 in
-- Extend both original integral arguments over the actual C_p coefficients.
/-- The entire two Lie images are orthogonal in X's original scalar Cartier pairing. -/
theorem rationalPlaceHodgeTateLeft_pairing_eq_zero
    (v : RationalPlaceHodgeTateLeftSource X) (w : RationalPlaceHodgeTateLeftSource X.cartierDual) :
    rationalPlaceTateScalarDuality X (rationalPlaceHodgeTateLeft X.cartierDual w)
      (rationalPlaceHodgeTateLeft X v) = 0 := by
  induction v using TensorProduct.inductionOn with
  | tmul c d =>
    induction w using TensorProduct.inductionOn with
    | tmul b e =>
      have hc : c ⊗ₜ[O] d = c • ((1 : ℂ_[p]) ⊗ₜ[O] d) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have hb : b ⊗ₜ[O] e = b • ((1 : ℂ_[p]) ⊗ₜ[O] e) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hc, hb]
      simp only [map_smul, LinearMap.smul_apply,
        rationalPlaceHodgeTateLeft_pairing_one_eq_zero, smul_zero]
    | add v w hv hw => simp only [map_add, LinearMap.add_apply, hv, hw, add_zero]
  | add v w hv hw => simp only [map_add, hv, hw, add_zero]

/-- Orthogonality also holds in the actual cyclotomic root line. -/
theorem rationalPlaceHodgeTateLeft_rootPairing_eq_zero
    (v : RationalPlaceHodgeTateLeftSource X) (w : RationalPlaceHodgeTateLeftSource X.cartierDual) :
    rationalPlaceTateRootDuality X (rationalPlaceHodgeTateLeft X.cartierDual w)
      (rationalPlaceHodgeTateLeft X v) = 0 := by
  apply (rationalPlaceRootCoordinate p).injective
  rw [map_zero]
  exact rationalPlaceHodgeTateLeft_pairing_eq_zero X v w
end ThreeAdicPlan
