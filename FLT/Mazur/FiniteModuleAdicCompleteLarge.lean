/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteModuleAdicComplete
public import Mathlib.RingTheory.Finiteness.Small

/-!
# Completeness for finite modules in larger universes

Proper cohomology lives one universe above its base ring. Shrinking finite
modules and the naturality of completion transport the finite-module result
without imposing an equality of universes on the geometric applications.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FiniteModuleAdicComplete

universe u v w

variable {R : Type u} [CommRing R] (J : Ideal R)
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]

/-- Completion maps of inverse linear equivalences are inverse on every completion element. -/
lemma map_equiv_symm (e : M ≃ₗ[R] N) (x : AdicCompletion J N) :
    AdicCompletion.map J e.toLinearMap (AdicCompletion.map J e.symm.toLinearMap x) = x := by
  have he : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
    ext y
    exact e.apply_symm_apply y
  rw [AdicCompletion.map_comp_apply, he, AdicCompletion.map_id]
  rfl

/-- Bijectivity of the original completion map is preserved by linear equivalence. -/
theorem of_bijective_of_equiv (e : M ≃ₗ[R] N)
    (h : Function.Bijective (AdicCompletion.of J M)) :
    Function.Bijective (AdicCompletion.of J N) := by
  constructor
  · intro x y hxy
    apply e.symm.injective
    apply h.1
    simpa only [AdicCompletion.map_of, LinearEquiv.coe_coe] using congrArg
      (AdicCompletion.map J e.symm.toLinearMap) hxy
  · intro x
    obtain ⟨y, hy⟩ := h.2 (AdicCompletion.map J e.symm.toLinearMap x)
    refine ⟨e y, ?_⟩
    change AdicCompletion.of J N (e.toLinearMap y) = x
    rw [← AdicCompletion.map_of, hy, map_equiv_symm]

/-- Every finite module over a complete Noetherian ring is complete, in any universe. -/
theorem isAdicComplete_large (M : Type v) [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [IsAdicComplete J R] [Module.Finite R M] : IsAdicComplete J M := by
  let _ : Small.{u} M := Module.Finite.small R M
  exact AdicCompletion.of_bijective_iff.mp
    (of_bijective_of_equiv J (Shrink.linearEquiv R M) (of_bijective J (Shrink.{u} M)))

end FLT.Mazur.FiniteModuleAdicComplete
