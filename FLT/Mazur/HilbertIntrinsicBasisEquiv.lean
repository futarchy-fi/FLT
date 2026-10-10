/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertIntrinsicBasisOpen

/-!
# Intrinsic basis opens under linear equivalences

Changing a model of a finitely presented module preserves the actual open
where a prescribed tuple is a basis. No global trivialization is required.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.HilbertChart

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

/-- A linear equivalence transports exactly the prescribed basis witnesses. -/
theorem tuple_basis_equiv_iff {ι : Type*} (e : M ≃ₗ[R] N) (y : ι → M) :
    (∃ b : Module.Basis ι R N, ∀ i, b i = e (y i)) ↔
      ∃ b : Module.Basis ι R M, ∀ i, b i = y i := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.map e.symm, fun i ↦ by rw [Module.Basis.map_apply, hb, e.symm_apply_apply]⟩
  · rintro ⟨b, hb⟩
    exact ⟨b.map e, fun i ↦ by rw [Module.Basis.map_apply, hb]⟩

variable [Module.FinitePresentation R M] [Module.FinitePresentation R N] {d : ℕ}

/-- Isomorphic models of the family have identical intrinsic basis opens. -/
theorem intrinsicBasisOpen_equiv (e : M ≃ₗ[R] N) (y : Fin d → M) :
    intrinsicBasisOpen (R := R) (e ∘ y) = intrinsicBasisOpen (R := R) y := by
  ext p
  change p ∈ intrinsicBasisOpen (R := R) (e ∘ y) ↔ p ∈ intrinsicBasisOpen (R := R) y
  rw [mem_intrinsicBasisOpen_iff, mem_intrinsicBasisOpen_iff]
  have h := tuple_basis_equiv_iff (e.baseChange R (Localization.AtPrime p.asIdeal))
    (fun i ↦ (1 : Localization.AtPrime p.asIdeal) ⊗ₜ[R] y i)
  simpa only [LinearEquiv.baseChange_tmul, Function.comp_apply] using h

end FLT.Mazur.HilbertChart
