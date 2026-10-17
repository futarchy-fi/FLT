/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarRestrictionImage
public import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Finiteness of a relative image with scalar restriction kernel

The scalar restriction image is cyclic. Consequently finiteness of the
relative connecting image is equivalent to finiteness of the boundary source
module after flat extension. No finiteness of the ambient equation module is
required, and no local finiteness is descended to the original ring.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ScalarRestrictionImage
variable {R D M : Type*} [CommRing R]
  [AddCommGroup D] [Module R D] [AddCommGroup M] [Module R M]
  (ρ : R →ₗ[R] D) (g : D →ₗ[R] M)
  (hker : LinearMap.ker g = LinearMap.range ρ)
  (S : Type*) [CommRing S] [Algebra R S] [Module.Flat R S]

include hker in
/-- A cyclic restriction kernel makes relative image finiteness equivalent to source finiteness. -/
theorem range_fg_iff_source_finite :
    (LinearMap.range (g.baseChange S)).FG ↔ Module.Finite S (S ⊗[R] D) := by
  constructor
  · intro hfg
    apply Module.finite_def.mpr
    apply Submodule.fg_of_fg_map_of_fg_inf_ker (g.baseChange S)
    · simpa only [Submodule.map_top] using hfg
    · rw [top_inf_eq, ScalarImageSourceGenerators.ker_baseChange ρ g hker S,
        range_eq_span_unit]
      exact Submodule.fg_span (Set.finite_singleton _)
  · intro hfin
    let _ := hfin
    have hfg := (Module.Finite.fg_top (R := S) (M := S ⊗[R] D)).map (g.baseChange S)
    simpa only [Submodule.map_top] using hfg

end FLT.Mazur.ScalarRestrictionImage
