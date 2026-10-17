/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarImageOriginalGenerators
public import Mathlib.RingTheory.Flat.Basic

/-!
# Finite local images from source generators modulo exact restrictions

For an exact pair of original maps, flat extension identifies relative source
spanning with image spanning. This provides a source-side finiteness criterion
without requiring finite generation of the ambient equation module.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ScalarImageSourceGenerators
variable {R U D M : Type*} [CommRing R]
  [AddCommGroup U] [Module R U] [AddCommGroup D] [Module R D]
  [AddCommGroup M] [Module R M]

/-- A submodule covers the image precisely when it spans the source modulo the kernel. -/
theorem map_eq_range_iff (g : D →ₗ[R] M) (E : Submodule R D) :
    E.map g = LinearMap.range g ↔ E ⊔ LinearMap.ker g = ⊤ := by
  constructor
  · intro h
    apply top_unique
    apply (LinearMap.map_le_map_iff g).mp
    rw [Submodule.map_top, h]
  · intro h
    apply le_antisymm (by rintro _ ⟨x, _, rfl⟩; exact ⟨x, rfl⟩)
    have he : (⊤ : Submodule R D).map g ≤ E.map g := by
      apply (LinearMap.map_le_map_iff g).mpr
      rw [h]
    simpa only [Submodule.map_top] using he

variable (ρ : U →ₗ[R] D) (g : D →ₗ[R] M)
  (hker : LinearMap.ker g = LinearMap.range ρ)
  (S : Type*) [CommRing S] [Algebra R S] [Module.Flat R S]

include hker in
/-- Flat extension preserves the original restriction image as the entire connecting kernel. -/
theorem ker_baseChange :
    LinearMap.ker (g.baseChange S) = LinearMap.range (ρ.baseChange S) := by
  apply LinearMap.exact_iff.mp
  exact Module.Flat.lTensor_exact S (LinearMap.exact_iff.mpr hker)

include hker in
/-- Finite original values span the local image exactly when they span modulo restrictions. -/
theorem original_span_iff {n : ℕ} (t : Fin n → D) :
    Submodule.span S (Set.range (fun j ↦ (1 ⊗ₜ[R] g (t j) : S ⊗[R] M))) =
        LinearMap.range (g.baseChange S) ↔
      Submodule.span S (Set.range (fun j ↦ (1 ⊗ₜ[R] t j : S ⊗[R] D))) ⊔
        LinearMap.range (ρ.baseChange S) = ⊤ := by
  have hm : (Submodule.span S (Set.range (fun j ↦ (1 ⊗ₜ[R] t j : S ⊗[R] D)))).map
      (g.baseChange S) =
      Submodule.span S (Set.range (fun j ↦ (1 ⊗ₜ[R] g (t j) : S ⊗[R] M))) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [← hm, map_eq_range_iff, ker_baseChange ρ g hker S]

include hker in
/-- Local image finiteness is finite original generation modulo restrictions. -/
theorem fg_iff_original_source_generators :
    (LinearMap.range (g.baseChange S)).FG ↔ ∃ (n : ℕ) (t : Fin n → D),
      Submodule.span S (Set.range (fun j ↦ (1 ⊗ₜ[R] t j : S ⊗[R] D))) ⊔
        LinearMap.range (ρ.baseChange S) = ⊤ := by
  rw [ScalarImageOriginalGenerators.fg_iff_original_generators]
  exact exists_congr fun n ↦ exists_congr fun t ↦ original_span_iff ρ g hker S t

end FLT.Mazur.ScalarImageSourceGenerators
