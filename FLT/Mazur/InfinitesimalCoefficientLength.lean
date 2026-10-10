/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NoetherianInfinitesimalFiberFunctions
public import FLT.Mazur.TensorInjectivityFiniteLength
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Finite length of infinitesimal coefficient modules

For a finite module over a Noetherian base, quotienting by a power of a maximal
ideal has finite length. The proof uses the actual quotient tensor equivalence
and the Artinian quotient ring, so it also applies to nonfree coefficients.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.InfinitesimalCoefficientLength
variable {R : Type} [CommRing R] [IsNoetherianRing R]
variable (C : Type) [AddCommGroup C] [Module R C] [Module.Finite R C]

/-- Finite coefficients modulo a maximal-ideal power have finite length. -/
theorem quotient_pow_finiteLength (I : Ideal R) [I.IsMaximal] (n : ℕ) :
    IsFiniteLength R (C ⧸ (I ^ n • ⊤ : Submodule R C)) := by
  let _ := NoetherianInfinitesimalFiberFunctions.quotient_pow_artinian I n
  let _ : IsArtinian R ((R ⧸ I ^ n) ⊗[R] C) :=
    isArtinian_of_surjective_algebraMap (R := R ⧸ I ^ n)
      (Ideal.Quotient.mk_surjective)
  let _ := isArtinian_of_surjective _ (quotTensorEquivQuotSMul C (I ^ n)).toLinearMap
    (quotTensorEquivQuotSMul C (I ^ n)).surjective
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

/-- Closed-fiber injectivity persists for every finite infinitesimal coefficient module. -/
theorem injective_quotient_pow [IsLocalRing R]
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Flat R N]
    (f : M →ₗ[R] N)
    (h : Function.Injective (f.lTensor (IsLocalRing.ResidueField R))) (n : ℕ) :
    Function.Injective (f.lTensor
      (C ⧸ ((IsLocalRing.maximalIdeal R) ^ n • ⊤ : Submodule R C))) :=
  TensorInjectivityFiniteLength.injective_of_closedFiber f h
    (quotient_pow_finiteLength C _ n)

end FLT.Mazur.InfinitesimalCoefficientLength
