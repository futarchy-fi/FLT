/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Prescribed bases through a tower of scalar extensions

The tensor cancellation equivalence identifies the iterated prescribed tuple
with the directly extended tuple, including its actual basis witnesses.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.HilbertChart

variable {R S T M : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
variable [AddCommGroup M] [Module R M]

/-- Iterated and direct scalar extension have exactly the same prescribed basis condition. -/
theorem tuple_basis_tower_iff {ι : Type*} (y : ι → M) :
    (∃ b : Module.Basis ι T (T ⊗[S] (S ⊗[R] M)),
      ∀ i, b i = (1 : T) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] y i)) ↔
    ∃ b : Module.Basis ι T (T ⊗[R] M), ∀ i, b i = (1 : T) ⊗ₜ[R] y i := by
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T M
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b.map e, fun i ↦ ?_⟩
    rw [Module.Basis.map_apply, hb]
    exact (TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul R S T _ _ _).trans
      (by rw [one_smul])
  · rintro ⟨b, hb⟩
    refine ⟨b.map e.symm, fun i ↦ ?_⟩
    rw [Module.Basis.map_apply, hb]
    exact TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul R S T _ _

end FLT.Mazur.HilbertChart
