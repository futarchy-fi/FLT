/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorKernelExtension
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Detecting tensor injectivity on infinitesimal coefficients

The kernel of reduction of a tensor coefficient module lies in the corresponding
ideal multiple of the tensor product. Adic separation therefore upgrades
injectivity on all infinitesimal reductions to injectivity before reduction.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.TensorAdicSeparation
variable {R C M N : Type*} [CommRing R]
  [AddCommGroup C] [Module R C] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Vanishing after coefficient reduction puts a tensor in the actual ideal multiple. -/
theorem mem_smul_of_reduction_zero (I : Ideal R) (x : C ⊗[R] M)
    (hx : (I • ⊤ : Submodule R C).mkQ.rTensor M x = 0) :
    x ∈ I • (⊤ : Submodule R (C ⊗[R] M)) := by
  obtain ⟨y, rfl⟩ := (rTensor_exact M
    (LinearMap.exact_subtype_mkQ (I • ⊤ : Submodule R C))
    (I • ⊤ : Submodule R C).mkQ_surjective x).mp hx
  clear hx
  induction y using TensorProduct.inductionOn with
  | tmul c m =>
    change c.val ⊗ₜ[R] m ∈ _
    exact Submodule.smul_top_le_comap_smul_top
      I ((TensorProduct.mk R C M).flip m) c.property
  | add a b ha hb =>
    rw [map_add]
    exact Submodule.add_mem _ ha hb

/-- A separated tensor product detects injectivity on all powers of an ideal. -/
theorem injective_of_quotient_pow (I : Ideal R) [IsHausdorff I (C ⊗[R] M)]
    (f : M →ₗ[R] N)
    (h : ∀ n : ℕ, Function.Injective (f.lTensor
      (C ⧸ (I ^ n • ⊤ : Submodule R C)))) :
    Function.Injective (f.lTensor C) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro x hx
  change x = 0
  apply IsHausdorff.haus (I := I) inferInstance x
  intro n
  apply SModEq.zero.mpr
  apply mem_smul_of_reduction_zero
  apply h n
  rw [map_zero, TensorKernelExtension.differential_naturality, hx, map_zero]

end FLT.Mazur.TensorAdicSeparation
