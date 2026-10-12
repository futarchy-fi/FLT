/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteModuleFiberVanishing
public import Mathlib.RingTheory.Flat.Basic

/-!
# Surjectivity of a finite module map from its residue fibers

The cokernel is finite, and right exactness of tensor product makes every
residue fiber of the cokernel zero. This detects surjectivity over arbitrary
coefficient rings, including nonreduced ones.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FiniteModuleFiberVanishing

variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Surjectivity of all prime residue fibers detects surjectivity onto a finite module. -/
theorem surjective_of_residue_fields (f : M →ₗ[R] N) [Module.Finite R N]
    (hf : ∀ p : PrimeSpectrum R, Function.Surjective (f.lTensor p.asIdeal.ResidueField)) :
    Function.Surjective f := by
  have h (p : PrimeSpectrum R) : Subsingleton (p.asIdeal.ResidueField ⊗[R] (N ⧸ f.range)) := by
    let K := p.asIdeal.ResidueField
    have he := lTensor_exact K (LinearMap.exact_map_mkQ_range f) f.range.mkQ_surjective
    have hz (x : K ⊗[R] (N ⧸ f.range)) : x = 0 := by
      obtain ⟨y, rfl⟩ := f.range.mkQ.lTensor_surjective K f.range.mkQ_surjective x
      exact (he y).mpr (hf p y)
    exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩
  let _ : Subsingleton (N ⧸ f.range) := subsingleton_of_residue_fields h
  exact LinearMap.range_eq_top.mp (Submodule.Quotient.subsingleton_iff.mp inferInstance)

end FLT.Mazur.FiniteModuleFiberVanishing
