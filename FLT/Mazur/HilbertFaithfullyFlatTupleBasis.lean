/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertLocalizedTupleBasis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Faithfully flat detection of prescribed bases

A tuple is a basis exactly when it becomes one after a faithfully flat scalar
extension. This applies in particular to extensions of residue fields.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.HilbertChart

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (S : Type*) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S] {d : ℕ}

/-- Faithfully flat extension detects the basis condition on the actual prescribed tuple. -/
theorem tuple_basis_iff_faithfullyFlat (y : Fin d → M) :
    (∃ b : Module.Basis (Fin d) R M, ∀ i, b i = y i) ↔
      ∃ b : Module.Basis (Fin d) S (S ⊗[R] M),
        ∀ i, b i = (1 : S) ⊗ₜ[R] y i := by
  let b := Pi.basisFun R (Fin d)
  let f := tupleLinearMap (R := R) y
  have hf (i) : f (b i) = y i := Module.Basis.constr_basis _ _ _ i
  have hg (i) : f.baseChange S (b.baseChange S i) = (1 : S) ⊗ₜ[R] y i := by
    rw [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul, hf]
  rw [show (∃ c : Module.Basis (Fin d) R M, ∀ i, c i = y i) ↔
      Function.Bijective f by simpa only [hf] using exists_mapped_basis_iff b f]
  rw [show (∃ c : Module.Basis (Fin d) S (S ⊗[R] M),
      ∀ i, c i = (1 : S) ⊗ₜ[R] y i) ↔ Function.Bijective (f.baseChange S) by
    simpa only [hg] using exists_mapped_basis_iff (b.baseChange S) (f.baseChange S)]
  exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective R S f).symm

end FLT.Mazur.HilbertChart
