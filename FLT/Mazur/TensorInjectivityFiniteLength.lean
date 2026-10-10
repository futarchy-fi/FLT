/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorKernelFiniteLength
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Injectivity with finite-length coefficients

For a map into a flat module, injectivity on residue coefficients propagates
through finite composition series. Over a local ring only its closed residue
field is needed. This supplies the infinitesimal step of the local flatness criterion.
-/

@[expose] public noncomputable section
open TensorProduct
universe v
namespace FLT.Mazur.TensorInjectivityFiniteLength
variable {R : Type v} [CommRing R]
variable {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module.Flat R N]
  (f : M →ₗ[R] N)

/-- Residue injectivity implies injectivity with every finite-length coefficient module. -/
theorem injective_of_residues
    (h : ∀ (I : Ideal R) [I.IsMaximal], Function.Injective (f.lTensor (R ⧸ I)))
    {C : Type v} [AddCommGroup C] [Module R C] (hC : IsFiniteLength R C) :
    Function.Injective (f.lTensor C) := by
  have he := TensorKernelFiniteLength.exact_of_residue_quotients
    (0 : M →ₗ[R] M) f (by simp) (fun I _ ↦ ?_) hC
  · simpa only [LinearMap.lTensor_zero, LinearMap.exact_zero_iff_injective] using he
  · simpa only [LinearMap.lTensor_zero, LinearMap.exact_zero_iff_injective] using h I

/-- Over a local base, the single closed residue field supplies all simple coefficients. -/
theorem injective_of_closedFiber [IsLocalRing R]
    (h : Function.Injective (f.lTensor (IsLocalRing.ResidueField R)))
    {C : Type v} [AddCommGroup C] [Module R C] (hC : IsFiniteLength R C) :
    Function.Injective (f.lTensor C) := by
  apply injective_of_residues f _ hC
  intro I hI
  rw [IsLocalRing.eq_maximalIdeal hI]
  exact h

end FLT.Mazur.TensorInjectivityFiniteLength
