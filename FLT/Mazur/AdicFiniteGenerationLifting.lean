/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteModuleAdicComplete
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Lifting finite generation from the closed quotient

Lift a finite free presentation of the closed quotient. Completeness of
the finite free source and separatedness of the original target make the
lift surjective. Finiteness of the target is a conclusion, not an input.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicFiniteGenerationLifting

universe u v

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
  [IsAdicComplete I R] (M : Type v) [AddCommGroup M] [Module R M] [IsHausdorff I M]

/-- Any lifted finite presentation of the closed quotient already generates the original module. -/
theorem surjective_of_closed (r : ℕ) (f : (Fin r → R) →ₗ[R] M)
    (hf : Function.Surjective ((I • (⊤ : Submodule R M)).mkQ ∘ₗ f)) :
    Function.Surjective f := by
  let _ := FiniteModuleAdicComplete.isAdicComplete I (Fin r → R)
  exact surjective_of_mkQ_comp_surjective hf

/-- A separated module with finite closed quotient is finite over the complete Noetherian base. -/
theorem finite_of_closed [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] :
    Module.Finite R M := by
  obtain ⟨r, f, hf⟩ := Module.Finite.exists_fin' R (M ⧸ (I • (⊤ : Submodule R M)))
  obtain ⟨g, hg⟩ := Module.projective_lifting_property
    (I • (⊤ : Submodule R M)).mkQ f (Submodule.mkQ_surjective _)
  exact Module.Finite.of_surjective g (surjective_of_closed I M r g (hg.symm ▸ hf))

end FLT.Mazur.AdicFiniteGenerationLifting
