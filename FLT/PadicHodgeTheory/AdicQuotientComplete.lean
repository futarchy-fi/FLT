/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # Adic precompleteness descends along surjective linear maps -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Surjective images of adically precomplete modules remain precomplete. -/
theorem adicPrecomplete_of_surjective [IsPrecomplete I M]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) : IsPrecomplete I N := by
  apply (AdicCompletion.of_surjective_iff (I := I) (M := N)).mp
  intro y
  have hq : Function.Surjective ((Submodule.mkQ (I • ⊤)) ∘ₗ f) :=
    (Submodule.mkQ_surjective _).comp hf
  obtain ⟨x, hx⟩ := AdicCompletion.map_surjective_of_mkQ_comp_surjective hq y
  obtain ⟨a, rfl⟩ := AdicCompletion.of_surjective I M x
  exact ⟨f a, by rwa [AdicCompletion.map_of] at hx⟩

/-- A quotient of an adically precomplete ring is precomplete as a module. -/
theorem adicPrecomplete_quotient [IsPrecomplete I R] (J : Ideal R) :
    IsPrecomplete I (R ⧸ J) :=
  adicPrecomplete_of_surjective I J.mkQ J.mkQ_surjective

/-- Ring formulation using the image ideal in the quotient. -/
theorem adicPrecomplete_quotient_map [IsPrecomplete I R] (J : Ideal R) :
    IsPrecomplete (I.map (Ideal.Quotient.mk J)) (R ⧸ J) := by
  let := adicPrecomplete_quotient I J
  exact (IsPrecomplete.map_algebraMap_iff (I := I)).mpr inferInstance

end PadicHodgeTheory
