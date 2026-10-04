/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Flat.LocalFlatCokernel
public import Mathlib.RingTheory.Regular.Category
public import Mathlib.RingTheory.QuotSMulTop

/-! # Fibre-regular elements give regular maps and flat quotients -/

@[expose] public noncomputable section

open TensorProduct
open scoped Pointwise

namespace Module.Flat

variable {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [IsNoetherianRing S] [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N] [Module.Finite S N] [Flat R N]

/-- A fibre-regular scalar on a finite module over a Noetherian local algebra
is regular on that module, and its quotient remains flat over the base. -/
theorem regular_and_flat_quotSMulTop_of_fibre (x : S)
    (hx : IsSMulRegular (N ⊗[R] (R ⧸ IsLocalRing.maximalIdeal R)) x) :
    IsSMulRegular N x ∧ Flat R (QuotSMulTop x N) := by
  let f := (LinearMap.lsmul S N x).restrictScalars R
  let g := (Submodule.mkQ (x • (⊤ : Submodule S N))).restrictScalars R
  have heq : f.rTensor (R ⧸ IsLocalRing.maximalIdeal R) =
      (LinearMap.lsmul S (N ⊗[R] (R ⧸ IsLocalRing.maximalIdeal R)) x).restrictScalars R := by
    exact TensorProduct.ext' fun n a ↦ (smul_tmul' x n a).symm
  have hf : Function.Injective (f.lTensor (R ⧸ IsLocalRing.maximalIdeal R)) := by
    rw [LinearMap.lTensor_inj_iff_rTensor_inj, heq]
    exact hx
  have hex : Function.Exact f g := LinearMap.exact_lsmul_mkQ_smul_top N x
  have hg : Function.Surjective g := Submodule.mkQ_surjective (x • (⊤ : Submodule S N))
  exact injective_and_flat_of_local_residue (R := R) (S := S) (N := N) (M := N)
    (Q := QuotSMulTop x N) f g hex hg hf

/-- For the algebra itself, the cokernel is the actual principal ideal quotient. -/
theorem regular_and_flat_quotient_of_fibre [Flat R S] (x : S)
    (hx : IsSMulRegular (S ⊗[R] (R ⧸ IsLocalRing.maximalIdeal R)) x) :
    IsSMulRegular S x ∧ Flat R (S ⧸ Ideal.span {x}) := by
  have h := regular_and_flat_quotSMulTop_of_fibre (R := R) (N := S) x hx
  have he : x • (⊤ : Submodule S S) = Ideal.span {x} := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  change IsSMulRegular S x ∧ Flat R (S ⧸ (x • (⊤ : Submodule S S))) at h
  rw [he] at h
  exact h

end Module.Flat
