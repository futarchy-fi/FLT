/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarImageSourceGenerators
public import Mathlib.RingTheory.Nakayama

/-!
# Lifting residue source generators modulo an exact restriction image

Nakayama is applied to the finite connecting image itself. Residue generation
in the source therefore lifts without an injectivity assumption on reduction
of the image inside an ambient module. Finiteness of the image is still required.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.SourceImageNakayama
variable {R U D M : Type*} [CommRing R]
  [AddCommGroup U] [Module R U] [AddCommGroup D] [Module R D]
  [AddCommGroup M] [Module R M]
  (ρ : U →ₗ[R] D) (g : D →ₗ[R] M)
  (hker : LinearMap.ker g = LinearMap.range ρ)

include hker in
/-- The restriction image disappears under the connecting map, including ideal multiples. -/
theorem map_source_sup (E : Submodule R D) (J : Ideal R) :
    (E ⊔ LinearMap.range ρ ⊔ J • (⊤ : Submodule R D)).map g =
      E.map g ⊔ J • LinearMap.range g := by
  rw [← hker, Submodule.map_sup, Submodule.map_sup, Submodule.map_smul'',
    Submodule.map_top, (LinearMap.le_ker_iff_map.mp le_rfl), sup_bot_eq]

include hker in
/-- Residue generation modulo exact restrictions lifts when the connecting image is finite. -/
theorem source_span_of_residue (hfg : (LinearMap.range g).FG)
    (E : Submodule R D) (J : Ideal R) (hJ : J ≤ Ideal.jacobson ⊥)
    (hres : E ⊔ LinearMap.range ρ ⊔ J • (⊤ : Submodule R D) = ⊤) :
    E ⊔ LinearMap.range ρ = ⊤ := by
  have hm := congrArg (Submodule.map g) hres
  rw [map_source_sup ρ g hker, Submodule.map_top] at hm
  have hle : LinearMap.range g ≤ E.map g :=
    Submodule.le_of_le_smul_of_le_jacobson_bot hfg hJ hm.ge
  rw [← hker, ← ScalarImageSourceGenerators.map_eq_range_iff]
  exact le_antisymm (by rintro _ ⟨x, _, rfl⟩; exact ⟨x, rfl⟩) hle

include hker in
/-- Surjectivity modulo an ideal in the Jacobson radical kills a finite connecting image. -/
theorem eq_zero_of_residue (hfg : (LinearMap.range g).FG)
    (J : Ideal R) (hJ : J ≤ Ideal.jacobson ⊥)
    (hres : LinearMap.range ρ ⊔ J • (⊤ : Submodule R D) = ⊤) : g = 0 := by
  have ht := source_span_of_residue ρ g hker hfg ⊥ J hJ (by simpa only [bot_sup_eq] using hres)
  rw [bot_sup_eq, ← hker] at ht
  exact LinearMap.ker_eq_top.mp ht

end FLT.Mazur.SourceImageNakayama
