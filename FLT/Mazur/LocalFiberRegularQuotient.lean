/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalFiberTensorInjectivity
public import FLT.Mazur.FlatCokernelResidueIdeals
public import FLT.Mazur.RelativeCartier

/-!
# The local fiberwise-regular flat-quotient criterion

For a flat local homomorphism of Noetherian local rings, an equation regular on
the closed fiber is regular in the ambient ring and has flat quotient over the
base. This is the converse algebraic input for relative Cartier divisors.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.LocalFiberRegularQuotient
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
  [IsNoetherianRing R] [IsNoetherianRing B] [IsLocalRing R] [IsLocalRing B]
  [IsLocalHom (algebraMap R B)] [Module.Flat R B]

/-- Closed-fiber regularity gives injectivity with all finite base coefficients. -/
theorem tensor_mul_injective (a : B)
    (ha : IsRegular (1 ⊗ₜ[R] a : IsLocalRing.ResidueField R ⊗[R] B))
    (C : Type) [AddCommGroup C] [Module R C] [Module.Finite R C] :
    Function.Injective (((LinearMap.mul B B a).restrictScalars R).lTensor C) := by
  apply LocalFiberTensorInjectivity.injective_finite _ _ C
  have he : (((LinearMap.mul B B a).restrictScalars R).lTensor
      (IsLocalRing.ResidueField R)) =
      LinearMap.mul R (IsLocalRing.ResidueField R ⊗[R] B) (1 ⊗ₜ[R] a) := by
    ext r b
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [he]
  exact ha.left

/-- An equation regular on the closed fiber is regular in the total local ring. -/
theorem regular (a : B)
    (ha : IsRegular (1 ⊗ₜ[R] a : IsLocalRing.ResidueField R ⊗[R] B)) :
    IsRegular a := by
  rw [← isLeftRegular_iff_isRegular]
  intro x y hxy
  have ht : (1 : R) ⊗ₜ[R] x = 1 ⊗ₜ[R] y :=
    tensor_mul_injective a ha R (by simpa using congrArg (fun b ↦ (1 : R) ⊗ₜ[R] b) hxy)
  simpa using congrArg (TensorProduct.lid R B) ht

/-- The full principal quotient is flat over the original local base. -/
theorem quotient_flat (a : B)
    (ha : IsRegular (1 ⊗ₜ[R] a : IsLocalRing.ResidueField R ⊗[R] B)) :
    Module.Flat R (B ⧸ Ideal.span {a}) :=
  FlatCokernelResidueIdeals.flat_of_quotient_injective
    ((LinearMap.mul B B a).restrictScalars R)
    (Ideal.Quotient.mkₐ R (Ideal.span {a})).toLinearMap
    (FCurve.exact_mul_quotient a) Ideal.Quotient.mk_surjective
    (fun I ↦ tensor_mul_injective a ha (R ⧸ I))

/-- Fiber regularity characterizes regular equations with flat quotient in the local setting. -/
theorem regular_iff_regular_and_flat (a : B) :
    IsRegular (1 ⊗ₜ[R] a : IsLocalRing.ResidueField R ⊗[R] B) ↔
      IsRegular a ∧ Module.Flat R (B ⧸ Ideal.span {a}) := by
  constructor
  · intro ha
    exact ⟨regular a ha, quotient_flat a ha⟩
  · rintro ⟨ha, hq⟩
    let _ := hq
    exact FCurve.isRegular_one_tmul_of_quotient_flat a ha (IsLocalRing.ResidueField R)

end FLT.Mazur.LocalFiberRegularQuotient
