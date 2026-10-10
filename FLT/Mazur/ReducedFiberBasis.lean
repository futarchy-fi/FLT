/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Detecting a basis on fibers over a reduced ring

A surjection from a finite free module is an isomorphism if every residue
fiber has the same dimension as the source. Reducedness removes relations
whose coordinates vanish in every residue field.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.ReducedFiberBasis

variable {R M ι : Type*} [CommRing R] [IsReduced R] [Nontrivial R]
  [AddCommGroup M] [Module R M] [Fintype ι]

omit [Nontrivial R] [Fintype ι] in
/-- Residue fields jointly detect vectors in a finite free module over a reduced ring. -/
theorem eq_zero_of_residue_tmul (x : ι →₀ R)
    (h : ∀ (p : Ideal R) [p.IsPrime],
      (1 : p.ResidueField) ⊗ₜ[R] x = 0) : x = 0 := by
  ext i
  apply IsNilpotent.eq_zero
  apply nilpotent_iff_mem_prime.mpr
  intro p hp
  let _ := hp
  apply Ideal.algebraMap_residueField_eq_zero.mp
  have he := congrArg ((Finsupp.lapply i : (ι →₀ R) →ₗ[R] R).baseChange p.ResidueField)
    (h p)
  have hz : (1 : p.ResidueField) ⊗ₜ[R] x i = 0 := by simpa using he
  simpa [Algebra.smul_def] using
    congrArg (Algebra.TensorProduct.rid R p.ResidueField p.ResidueField) hz

/-- A spanning family of the correct dimension in every fiber has no relations. -/
theorem bijective_of_surjective_of_fiber_dimension (f : (ι →₀ R) →ₗ[R] M)
    (hf : Function.Surjective f)
    (hd : ∀ (p : Ideal R) [p.IsPrime],
      Module.finrank p.ResidueField (p.ResidueField ⊗[R] M) = Fintype.card ι) :
    Function.Bijective f := by
  let _ : Module.Finite R M := Module.Finite.of_surjective f hf
  refine ⟨?_, hf⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply eq_zero_of_residue_tmul x
  intro p _
  have he : Module.finrank p.ResidueField (p.ResidueField ⊗[R] (ι →₀ R)) =
      Module.finrank p.ResidueField (p.ResidueField ⊗[R] M) := by
    rw [Module.finrank_baseChange, Module.finrank_finsupp_self, hd p]
  have hi := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := f.baseChange p.ResidueField) he).mpr (f.lTensor_surjective p.ResidueField hf)
  apply hi
  simp [hx]

end FLT.Mazur.ReducedFiberBasis
