/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SubmoduleReductionKernel
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Flat quotients preserve the reduced inclusion

Flatness of the quotient by the error image, rather than flatness of the
residue algebra, suffices to preserve the inclusion after reduction.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.SubmoduleReduction
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (J : Ideal R) (Q : Submodule R M)

/-- The reduced inclusion agrees with tensoring the actual inclusion by the residue algebra. -/
theorem inclusion_tensor (x : (R ⧸ J) ⊗[R] Q) :
    inclusion J Q (quotTensorEquivQuotSMul Q J x) =
      quotTensorEquivQuotSMul M J (Q.subtype.lTensor (R ⧸ J) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    simp only [quotTensorEquivQuotSMul_mk_tmul, LinearMap.lTensor_tmul,
      ← Submodule.mkQ_apply, inclusion_mk]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A flat ambient quotient supplies injectivity without assuming the residue algebra is flat. -/
theorem inclusion_injective_of_flat_quotient [Module.Flat R (M ⧸ Q)] :
    Function.Injective (inclusion J Q) := by
  have ht := LinearMap.lTensor_injective_of_exact_of_flat Q.mkQ Q.mkQ_surjective
    Q.subtype Q.injective_subtype (by
      intro x
      constructor
      · intro hx
        exact ⟨⟨x, (Submodule.Quotient.mk_eq_zero Q).mp hx⟩, rfl⟩
      · rintro ⟨y, rfl⟩
        exact (Submodule.Quotient.mk_eq_zero Q).mpr y.property) (R ⧸ J)
  intro x y h
  obtain ⟨x, rfl⟩ := (quotTensorEquivQuotSMul Q J).surjective x
  obtain ⟨y, rfl⟩ := (quotTensorEquivQuotSMul Q J).surjective y
  rw [inclusion_tensor, inclusion_tensor] at h
  exact congrArg (quotTensorEquivQuotSMul Q J)
    (ht ((quotTensorEquivQuotSMul M J).injective h))

/-- Flatness of the quotient gives the exact internal intersection identity. -/
theorem inf_smul_top_of_flat_quotient [Module.Flat R (M ⧸ Q)] :
    Q ⊓ J • (⊤ : Submodule R M) = J • Q :=
  (inclusion_injective_iff J Q).mp (inclusion_injective_of_flat_quotient J Q)

end FLT.Mazur.SubmoduleReduction
