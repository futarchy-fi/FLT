/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianPrincipalSeparation

/-!
# Recovering the entire original relation from principal-local quotients

For every coefficient principal cover, the global relation is exactly the
intersection of the inverse images of its localized functor relations.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] {d : ℕ}

/-- Principal-local membership in all actual functor relations detects original membership. -/
theorem grassmannian_mem_iff_localized_cover {ι : Type*} (r : ι → A)
    (hr : Ideal.span (Set.range r) = ⊤)
    (N : Module.Grassmannian A (A ⊗[R] M) d) (x : A ⊗[R] M) :
    x ∈ N.toSubmodule ↔ ∀ i,
      AlgebraTensorModule.rTensor R M (Algebra.linearMap A (Localization.Away (r i))) x ∈
        (Module.Grassmannian.map
          (IsScalarTower.toAlgHom R A (Localization.Away (r i))) N).toSubmodule := by
  constructor
  · intro hx i
    change _ ∈ (Module.Grassmannian.map
      (IsScalarTower.toAlgHom R A (Localization.Away (r i))) N).toSubmodule.restrictScalars A
    rw [grassmannian_localized_relation]
    exact ⟨x, hx, 1, by simp⟩
  · intro hx
    apply Submodule.mem_of_isLocalized_span (Set.range r) hr
      (fun s ↦ Localization.Away s.val ⊗[R] M)
      (fun s ↦ AlgebraTensorModule.rTensor R M
        (Algebra.linearMap A (Localization.Away s.val)))
    rintro ⟨a, i, rfl⟩
    rw [← grassmannian_localized_relation]
    exact hx i

/-- The full global relation is the intersection of all its actual local inverse images. -/
theorem grassmannian_relation_eq_iInf {ι : Type*} (r : ι → A)
    (hr : Ideal.span (Set.range r) = ⊤)
    (N : Module.Grassmannian A (A ⊗[R] M) d) :
    N.toSubmodule = ⨅ i, Submodule.comap
      (AlgebraTensorModule.rTensor R M (Algebra.linearMap A (Localization.Away (r i))))
      ((Module.Grassmannian.map
        (IsScalarTower.toAlgHom R A (Localization.Away (r i)))
        N).toSubmodule.restrictScalars A) := by
  ext x
  simp only [Submodule.mem_iInf, Submodule.mem_comap, Submodule.restrictScalars_mem]
  exact grassmannian_mem_iff_localized_cover r hr N x

end FLT.Mazur.GrassmannianChart
