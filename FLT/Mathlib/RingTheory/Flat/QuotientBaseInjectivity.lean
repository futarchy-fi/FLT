/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Flat.AdicBaseIdealInduction
public import FLT.Mathlib.RingTheory.Flat.AdicSubmoduleClosed
public import FLT.Mathlib.RingTheory.Flat.QuotientTensorInjectivity
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Residual injectivity survives every base-ideal quotient -/

@[expose] public noncomputable section

namespace Module.Flat

variable {R S N M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  [AddCommGroup M] [Module R M] [IsNoetherianRing S] [Module.Finite S N]
  [Flat R M]

/-- Over a finite Noetherian source module, residual injectivity implies
injectivity modulo every ideal contained in the chosen maximal ideal. -/
theorem lTensor_quotient_injective_of_le
    (I J : Ideal R) [I.IsMaximal] (hJI : J ≤ I)
    (hI : I.map (algebraMap R S) ≤ Ideal.jacobson ⊥)
    (f : N →ₗ[R] M) (hf : Function.Injective (f.lTensor (R ⧸ I))) :
    Function.Injective (f.lTensor (R ⧸ J)) := by
  apply (f.lTensor_quotient_injective_iff J).mpr
  intro x hx
  have hmem (n : ℕ) : x ∈ (J ⊔ I ^ n) • (⊤ : Submodule R N) := by
    cases n with
    | zero => simp
    | succ n =>
      apply (f.lTensor_quotient_injective_iff _).mp
        (lTensor_quotient_sup_pow_injective I J hJI f hf n) x
      exact (Submodule.smul_mono_left (show J ≤ J ⊔ I ^ (n + 1) from le_sup_left)) hx
  let P := J.map (algebraMap R S) • (⊤ : Submodule S N)
  have hclosed : x ∈ P := by
    apply P.mem_of_forall_mem_sup_pow_smul (I.map (algebraMap R S)) hI
    intro n
    have he := Ideal.smul_restrictScalars (J ⊔ I ^ n) (⊤ : Submodule S N)
    simp only [Submodule.restrictScalars_top, Ideal.map_sup, Ideal.map_pow,
      Submodule.sup_smul] at he
    change x ∈ (P ⊔ (I.map (algebraMap R S)) ^ n • (⊤ : Submodule S N)).restrictScalars R
    rw [show (P ⊔ (I.map (algebraMap R S)) ^ n • (⊤ : Submodule S N)).restrictScalars R =
      (J ⊔ I ^ n) • (⊤ : Submodule R N) from by simpa only [Submodule.sup_smul] using he]
    exact hmem n
  have he := Ideal.smul_restrictScalars J (⊤ : Submodule S N)
  simp only [Submodule.restrictScalars_top] at he
  change x ∈ P.restrictScalars R at hclosed
  rwa [he] at hclosed

/-- For a local base, every proper ideal lies in its maximal ideal. Hence
residual injectivity implies injectivity modulo every base ideal. -/
theorem lTensor_quotient_injective_of_local_residue [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] (f : N →ₗ[R] M)
    (hf : Function.Injective (f.lTensor (R ⧸ IsLocalRing.maximalIdeal R)))
    (J : Ideal R) : Function.Injective (f.lTensor (R ⧸ J)) := by
  by_cases hJ : J = ⊤
  · subst J
    apply (f.lTensor_quotient_injective_iff ⊤).mpr
    simp
  · exact lTensor_quotient_injective_of_le (S := S) (IsLocalRing.maximalIdeal R) J
      (IsLocalRing.le_maximalIdeal hJ)
      ((IsLocalRing.map_maximalIdeal_le (algebraMap R S)).trans
        (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal S))) f hf

end Module.Flat
