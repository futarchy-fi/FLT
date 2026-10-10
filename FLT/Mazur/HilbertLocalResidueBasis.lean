/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Lifting a prescribed residue basis over a local ring

Flatness supplies linear independence and Nakayama supplies spanning. Thus a
finite flat module has the prescribed basis exactly when its residue fiber does.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.HilbertChart

variable {R M : Type*} [CommRing R] [IsLocalRing R]
variable [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M]

/-- A prescribed tuple is a basis if and only if it is a basis in the residue fiber. -/
theorem local_basis_iff_residue_basis {ι : Type*} (y : ι → M) :
    (∃ b : Module.Basis ι R M, ∀ i, b i = y i) ↔
      ∃ b : Module.Basis ι (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField R ⊗[R] M),
        ∀ i, b i = (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] y i := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.baseChange _, fun i ↦ by rw [Module.Basis.baseChange_apply, hb]⟩
  · rintro ⟨b, hb⟩
    have hli := b.linearIndependent
    rw [show (b : ι → _) = TensorProduct.mk R _ M 1 ∘ y from funext hb] at hli
    have hl := Module.IsLocalRing.linearIndependent_of_flat y hli
    have hs := IsLocalRing.span_eq_top_of_tmul_eq_basis y b (fun i ↦ (hb i).symm)
    exact ⟨Module.Basis.mk hl hs.ge, fun i ↦ Module.Basis.mk_apply _ _ i⟩

end FLT.Mazur.HilbertChart
