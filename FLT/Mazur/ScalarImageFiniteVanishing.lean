/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarImageOriginalGenerators

/-!
# Finite tests for vanishing of a scalar image

An explicitly supplied finite local spanning family detects zero of the whole
map. A pointwise comparison transports the tests to concrete geometric errors
without unfolding their module structure inside the finite-generation proof.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ScalarImageFiniteVanishing
variable {R D M : Type*} [CommRing R]
  [AddCommGroup D] [Module R D] [AddCommGroup M] [Module R M]
  (g : D →ₗ[R] M) (S : Type*) [CommRing S] [Algebra R S]

/-- Original values spanning the scalar image detect vanishing of that entire image. -/
theorem eq_zero_iff {n : ℕ} (t : Fin n → D)
    (hspan : Submodule.span S
      (Set.range (fun j ↦ (1 ⊗ₜ[R] g (t j) : S ⊗[R] M))) =
        LinearMap.range (g.baseChange S)) :
    g.baseChange S = 0 ↔ ∀ j, (1 ⊗ₜ[R] g (t j) : S ⊗[R] M) = 0 := by
  constructor
  · intro h j
    exact (ScalarExtensionImageReduction.baseChange_eq_zero_iff g S).mp h (t j)
  · intro h
    apply LinearMap.range_eq_bot.mp
    apply le_bot_iff.mp
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact h j

/-- Finite local images supply finite tests in any pointwise equivalent geometric formulation. -/
theorem exists_tests (P : D → Prop)
    (hP : ∀ t, (1 ⊗ₜ[R] g t : S ⊗[R] M) = 0 ↔ P t)
    (hfg : (LinearMap.range (g.baseChange S)).FG) :
    ∃ (n : ℕ) (t : Fin n → D), (g.baseChange S = 0 ↔ ∀ j, P (t j)) := by
  obtain ⟨n, t, ht⟩ := ScalarImageOriginalGenerators.exists_original_generators g S hfg
  exact ⟨n, t, (eq_zero_iff g S t ht).trans (forall_congr' fun j ↦ hP (t j))⟩

end FLT.Mazur.ScalarImageFiniteVanishing
