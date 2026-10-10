/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ResidueVectorRetraction
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Splitting a free-module line from its actual residue tensors

The base-changed basis identifies the coordinates of the actual tensor
`1 ⊗ v` with the residues of the original coefficients. Nonvanishing in all
residue fibers therefore constructs a linear retraction over the original ring.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.FreeModuleResidueRetraction
universe u v w
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {ι : Type w} (b : Module.Basis ι R M) (v : M)

/-- A nonzero actual residue tensor has a nonzero vector of residue coordinates. -/
lemma residue_coordinates_ne_zero (p : PrimeSpectrum R)
    (h : (1 : p.asIdeal.ResidueField) ⊗ₜ[R] v ≠ 0) :
    (fun i ↦ algebraMap R p.asIdeal.ResidueField (b.repr v i)) ≠ 0 := by
  intro hz
  apply h
  apply (b.baseChange p.asIdeal.ResidueField).repr.injective
  ext i
  simpa only [Module.Basis.baseChange_repr_tmul, map_zero, Finsupp.zero_apply,
    Algebra.smul_def, mul_one, Pi.zero_apply] using congrFun hz i

include b in
/-- Residue nonvanishing constructs an actual functional taking value one on the vector. -/
lemma exists_functional_of_residue_tensor_ne_zero
    (h : ∀ p : PrimeSpectrum R, (1 : p.asIdeal.ResidueField) ⊗ₜ[R] v ≠ 0) :
    ∃ φ : M →ₗ[R] R, φ v = 1 := by
  obtain ⟨φ, hφ⟩ := ResidueVectorRetraction.exists_functional_of_residue_ne_zero
    (fun i ↦ b.repr v i) (fun p ↦ residue_coordinates_ne_zero b v p (h p))
  exact ⟨φ.comp (Finsupp.lcoeFun.comp b.repr.toLinearMap), hφ⟩

include b in
/-- The original line map is split over the coefficient ring, not merely over its residue fields. -/
lemma exists_retraction_of_residue_tensor_ne_zero
    (h : ∀ p : PrimeSpectrum R, (1 : p.asIdeal.ResidueField) ⊗ₜ[R] v ≠ 0) :
    ∃ φ : M →ₗ[R] R, φ.comp (LinearMap.toSpanSingleton R M v) = LinearMap.id := by
  obtain ⟨φ, hφ⟩ := exists_functional_of_residue_tensor_ne_zero b v h
  refine ⟨φ, LinearMap.ext fun r ↦ ?_⟩
  change φ (r • v) = r
  rw [map_smul, hφ, smul_eq_mul, mul_one]

end FLT.Mazur.FreeModuleResidueRetraction
