/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.QuotSMulTop

/-! # Scalar quotients commute with tensoring over a smaller base -/

@[expose] public noncomputable section

open TensorProduct

namespace QuotSMulTop

variable {R S N K : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  [AddCommGroup K] [Module R K]

/-- Taking the quotient by an `S`-scalar commutes with tensoring over `R`.
The equivalence is `S`-linear, so it transports the remaining regular sequence. -/
def relativeTensorEquiv (x : S) :
    QuotSMulTop x N ⊗[R] K ≃ₗ[S] QuotSMulTop x (N ⊗[R] K) :=
  (AlgebraTensorModule.cancelBaseChange R S S (QuotSMulTop x N) K).symm ≪≫ₗ
    quotSMulTopTensorEquivQuotSMulTop x (S ⊗[R] K) N ≪≫ₗ
      QuotSMulTop.congr x (AlgebraTensorModule.cancelBaseChange R S S N K)

@[simp]
theorem relativeTensorEquiv_mk_tmul (x : S) (n : N) (k : K) :
    relativeTensorEquiv (R := R) (K := K) x (Submodule.Quotient.mk n ⊗ₜ k) =
      Submodule.Quotient.mk (n ⊗ₜ[R] k) := by
  simp only [relativeTensorEquiv, quotSMulTopTensorEquivQuotSMulTop, equivQuotTensor,
    LinearEquiv.trans_symm, LinearEquiv.symm_symm, QuotSMulTop.congr, LinearEquiv.trans_apply,
    AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearEquiv.rTensor_tmul,
    Submodule.quotEquivOfEq_mk, quotTensorEquivQuotSMul_symm_mk, assoc_tmul,
    quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.equiv_apply]
  change Submodule.Quotient.mk ((1 : S) • n ⊗ₜ[R] k) = _
  rw [one_smul]

end QuotSMulTop
