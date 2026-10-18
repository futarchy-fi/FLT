/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SplitSubmoduleReduction

/-!
# Internal reduction of a stable split summand

A retraction preserving a boundary submodule splits its residual part inside
that submodule. Ideal divisibility here is internal to the boundary module;
it does not assert divisibility of arbitrary boundary elements in the ambient module.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.SplitSubmoduleReduction
variable {R M C : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup C]
  [Module R M] [Module R C] (i : C →ₗ[R] M) (r : M →ₗ[R] C)
  (hr : r.comp i = LinearMap.id) (N : Submodule R M)
  (hN : ∀ x ∈ N, i (r x) ∈ N)

/-- Extend exactly the residual coordinates whose extension belongs to the boundary. -/
def internalExtension : N.comap i →ₗ[R] N :=
  (i.comp (N.comap i).subtype).codRestrict N fun x ↦ x.property

/-- Stability constructs restriction on the boundary itself. -/
def internalRestriction : N →ₗ[R] N.comap i :=
  (r.comp N.subtype).codRestrict (N.comap i) fun x ↦ hN x x.property

include hr

/-- The boundary restriction and extension retain the original splitting. -/
theorem internal_split :
    (internalRestriction i r N hN).comp (internalExtension i N) = LinearMap.id := by
  ext x
  exact LinearMap.congr_fun hr x.val

omit hr in
/-- The internal residual range consists exactly of supported boundary elements. -/
theorem mem_internal_range_iff (x : N) :
    x ∈ LinearMap.range (internalExtension i N) ↔ x.val ∈ LinearMap.range i := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c.val, rfl⟩
  · rintro ⟨c, hc⟩
    refine ⟨⟨c, ?_⟩, ?_⟩
    · change i c ∈ N
      rw [hc]
      exact x.property
    · exact Subtype.ext hc

include hN

/-- Internal ideal multiples are absorbed by the actual residual boundary summand. -/
theorem internal_range_inf_smul_top (J : Ideal R) :
    LinearMap.range (internalExtension i N) ⊓ J • (⊤ : Submodule R N) =
      J • LinearMap.range (internalExtension i N) :=
  range_inf_smul_top _ _ (internal_split i r hr N hN) J

/-- Reduction inside the boundary cannot lose a supported boundary coefficient. -/
theorem internal_reduction_injective (J : Ideal R) :
    Function.Injective (SubmoduleReduction.inclusion J
      (LinearMap.range (internalExtension i N))) :=
  reduced_range_injective _ _ (internal_split i r hr N hN) J

end FLT.Mazur.SplitSubmoduleReduction
