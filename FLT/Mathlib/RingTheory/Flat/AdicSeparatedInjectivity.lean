/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Flat.AdicInjectivityInduction
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Krull intersection upgrades residual injectivity to injectivity -/

@[expose] public noncomputable section

open TensorProduct

namespace Module.Flat

variable {R S N M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  [AddCommGroup M] [Module R M]

/-- A kernel element lies in every positive adic power when its map has flat
target and is injective on the residue module. -/
theorem mem_pow_smul_of_map_eq_zero [Flat R M] (I : Ideal R) [I.IsMaximal]
    (f : N →ₗ[R] M) (hf : Function.Injective (f.lTensor (R ⧸ I)))
    {x : N} (hx : f x = 0) (n : ℕ) : x ∈ I ^ n • (⊤ : Submodule R N) := by
  cases n with
  | zero => simp
  | succ n =>
    have h : (1 : R ⧸ I ^ (n + 1)) ⊗ₜ[R] x = 0 :=
      lTensor_quotient_pow_injective I f hf n (by simp [hx])
    have := congrArg (quotTensorEquivQuotSMul N (I ^ (n + 1))) h
    simpa using this

/-- Finite modules over a Noetherian ring are separated for any base ideal
whose extension lies in the Jacobson radical. -/
theorem injective_of_residue_injective [IsNoetherianRing S] [Module.Finite S N]
    [Flat R M] (I : Ideal R) [I.IsMaximal]
    (hI : I.map (algebraMap R S) ≤ Ideal.jacobson ⊥)
    (f : N →ₗ[R] M) (hf : Function.Injective (f.lTensor (R ⧸ I))) :
    Function.Injective f := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  have hsep := (I.map (algebraMap R S)).iInf_pow_smul_eq_bot_of_le_jacobson (M := N) hI
  have hmem : x ∈ (⨅ n : ℕ, (I.map (algebraMap R S)) ^ n • ⊤ : Submodule S N) := by
    simp only [Submodule.mem_iInf]
    intro n
    have h := mem_pow_smul_of_map_eq_zero I f hf hx n
    have he := Ideal.smul_restrictScalars (I ^ n) (⊤ : Submodule S N)
    simp only [Submodule.restrictScalars_top, Ideal.map_pow] at he
    change x ∈ ((I.map (algebraMap R S)) ^ n • (⊤ : Submodule S N)).restrictScalars R
    rw [he]
    exact h
  simpa [hsep] using hmem

/-- The local version: no Noetherian assumption on the base is needed for
injectivity into a flat module. -/
theorem injective_of_local_residue_injective [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing S] [Module.Finite S N]
    [Flat R M] (f : N →ₗ[R] M)
    (hf : Function.Injective (f.lTensor (R ⧸ IsLocalRing.maximalIdeal R))) :
    Function.Injective f :=
  injective_of_residue_injective (R := R) (S := S) (N := N) (M := M)
    (IsLocalRing.maximalIdeal R)
    ((IsLocalRing.map_maximalIdeal_le (algebraMap R S)).trans
      (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal S))) f hf

end Module.Flat
