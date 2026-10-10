/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InfinitesimalCoefficientLength
public import FLT.Mazur.TensorAdicSeparation
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Closed-fiber injectivity over a Noetherian local algebra

For a flat local map of Noetherian local rings, injectivity on the closed fiber
of an endomorphism of the ambient algebra implies injectivity with every finite
base coefficient module. Krull intersection on the finite base-changed module
provides separation; no flatness of the endomorphism's cokernel is assumed.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.LocalFiberTensorInjectivity

/-- Adic separation descends along an injective linear map. -/
theorem hausdorff_of_injective {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (I : Ideal R) [IsHausdorff I N] (e : M →ₗ[R] N) (he : Function.Injective e) :
    IsHausdorff I M := by
  constructor
  intro x hx
  apply he
  rw [map_zero]
  apply IsHausdorff.haus (I := I) inferInstance (e x)
  intro n
  apply SModEq.zero.mpr
  exact Submodule.smul_top_le_comap_smul_top (I ^ n) e (SModEq.zero.mp (hx n))

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
  [IsNoetherianRing R] [IsNoetherianRing B] [IsLocalRing R] [IsLocalRing B]
  [IsLocalHom (algebraMap R B)] [Module.Flat R B]

omit [IsNoetherianRing R] [Module.Flat R B] in
/-- Krull intersection supplies separation for finite base coefficients. -/
theorem tensor_hausdorff (C : Type) [AddCommGroup C] [Module R C] [Module.Finite R C] :
    IsHausdorff (IsLocalRing.maximalIdeal R) (C ⊗[R] B) := by
  let _ : IsHausdorff (IsLocalRing.maximalIdeal R) (B ⊗[R] C) :=
    IsHausdorff.of_map (S := B) (IsLocalRing.map_maximalIdeal_le (algebraMap R B))
  exact hausdorff_of_injective _ (TensorProduct.comm R C B).toLinearMap
    (TensorProduct.comm R C B).injective

/-- A closed-fiber injection stays injective with every finite base coefficient module. -/
theorem injective_finite (f : B →ₗ[R] B)
    (h : Function.Injective (f.lTensor (IsLocalRing.ResidueField R)))
    (C : Type) [AddCommGroup C] [Module R C] [Module.Finite R C] :
    Function.Injective (f.lTensor C) := by
  let _ := tensor_hausdorff (R := R) (B := B) C
  exact TensorAdicSeparation.injective_of_quotient_pow (IsLocalRing.maximalIdeal R) f
    (InfinitesimalCoefficientLength.injective_quotient_pow C f h)

end FLT.Mazur.LocalFiberTensorInjectivity
