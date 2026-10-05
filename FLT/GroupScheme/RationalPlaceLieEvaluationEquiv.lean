/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceHodgeTateLeft

/-! # The actual Lie-cotangent pairing is perfect after scalar extension -/

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

/-- Finite freeness identifies the original Lie realization with the full cotangent dual. -/
def rationalPlaceLieEvaluationEquiv : RationalPlaceHodgeTateLeftSource X ≃ₗ[ℂ_[p]]
    Module.Dual ℂ_[p] (ℂ_[p] ⊗[O] X.cotangentLimit) := by
  let := rationalPlace_cotangentLimit_free X
  let := rationalPlace_cotangentLimit_finite X
  exact (TensorProduct.isBaseChange O X.cotangentLimit ℂ_[p]).toDualBaseChange

set_option maxHeartbeats 800000 in
-- Hom base change retains the original Lie scalar structures.
/-- The equivalence is the evaluation map already used to define the actual left map. -/
theorem rationalPlaceLieEvaluationEquiv_eq :
    (rationalPlaceLieEvaluationEquiv X).toLinearMap = rationalPlaceLieEvaluation X := by
  let := rationalPlace_cotangentLimit_free X
  let := rationalPlace_cotangentLimit_finite X
  apply TensorProduct.AlgebraTensorModule.ext
  intro c d
  apply LinearMap.ext
  intro w
  induction w using TensorProduct.inductionOn with
  | tmul b w =>
    have hb : b ⊗ₜ[O] w = b • ((1 : ℂ_[p]) ⊗ₜ[O] w) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hb, map_smul, map_smul]
    change b * ((TensorProduct.isBaseChange O X.cotangentLimit ℂ_[p]).toDualBaseChange
      (c ⊗ₜ d) (1 ⊗ₜ w)) = _
    have h := (TensorProduct.isBaseChange O X.cotangentLimit ℂ_[p]).toDualBaseChange_tmul c d w
    change (TensorProduct.isBaseChange O X.cotangentLimit ℂ_[p]).toDualBaseChange
      (c ⊗ₜ d) (1 ⊗ₜ w) = c * algebraMap O ℂ_[p] (d w) at h
    rw [h]
    simp only [rationalPlaceLieEvaluation_tmul, mul_one, smul_eq_mul]
  | add v w hv hw => simp only [map_add, hv, hw]

/-- The full cotangent realization is finite dimensional over C_p. -/
theorem rationalPlace_cotangentRealization_finite :
    Module.Finite ℂ_[p] (ℂ_[p] ⊗[O] X.cotangentLimit) := by
  let := rationalPlace_cotangentLimit_finite X
  exact Module.Finite.base_change O ℂ_[p] _
end ThreeAdicPlan
