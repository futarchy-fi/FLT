/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleTateFree
public import FLT.Deformations.RepresentationTheory.PadicPowerCardinality

/-! # The height is the rank of the original Tate module -/

@[expose] public noncomputable section
open scoped Pointwise TensorProduct
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- The standard p-adic filtration is exactly the actual evaluation kernel. -/
theorem tateEvalLinear_ker_ideal (n : ℕ) :
    LinearMap.ker (X.tateEvalLinear n) =
      Ideal.span {(p : ℤ_[p]) ^ n} • (⊤ : Submodule ℤ_[p] X.tateSequences) := by
  ext x
  rw [LinearMap.mem_ker, X.tateEvalLinear_eq_zero_iff,
    Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

/-- Tensor reduction retains the original finite group and p-adic scalar action. -/
def tateQuotientTensorEquiv (n : ℕ) :
    ((ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ n}) ⊗[ℤ_[p]] X.tateSequences) ≃ₗ[ℤ_[p]]
      (X.level n).Points :=
  (TensorProduct.quotTensorEquivQuotSMul X.tateSequences _).trans
    ((Submodule.quotEquivOfEq _ _ (X.tateEvalLinear_ker_ideal n).symm).trans
      ((X.tateEvalLinear n).quotKerEquivOfSurjective (X.tateEval_surjective_unconditional n)))

/-- The tensor comparison is the actual Tate evaluation on the unit pure tensor. -/
theorem tateQuotientTensorEquiv_one_tmul (n : ℕ) (x : X.tateSequences) :
    X.tateQuotientTensorEquiv n (1 ⊗ₜ x) = X.tateEvalLinear n x := by
  simp only [tateQuotientTensorEquiv, LinearEquiv.trans_apply,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
  rfl

/-- The rank of the actual Tate module equals the original integral system height. -/
theorem tateSequences_finrank : Module.finrank ℤ_[p] X.tateSequences = height := by
  let : Module.Finite ℤ_[p] X.tateSequences := X.tateSequences_finite
  let : Module.Free ℤ_[p] X.tateSequences := X.tateSequences_free
  have he := Nat.card_congr (X.tateQuotientTensorEquiv 1).toEquiv
  rw [GaloisRepresentation.PrimePower.card_baseChange,
    GaloisRepresentation.PrimePower.card_padic_quotient, ← FF.coordinate_finrank,
    X.rank, one_mul, pow_one] at he
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le) he
end ThreeAdicPlan.PDivisibleSystem
