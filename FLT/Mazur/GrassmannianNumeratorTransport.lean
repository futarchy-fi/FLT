/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

import all Mathlib.RingTheory.Grassmannian

public import FLT.Mazur.GrassmannianLocalizedRelation
public import FLT.Mazur.PrincipalSubmodulePatching

/-!
# Transport and denominator clearing of original quotient numerators

Coefficient extension preserves the full original relation. In a principal
localization, membership of a numerator is equivalent to membership after
multiplying by some power of the coefficient.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A B M : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [AddCommGroup M] [Module R M] {d : ℕ}

/-- Any coefficient algebra map preserves membership in the full original relation. -/
theorem grassmannian_map_numerator_mem (g : A →ₐ[R] B)
    (N : Module.Grassmannian A (A ⊗[R] M) d) (x : A ⊗[R] M)
    (hx : x ∈ N.toSubmodule) :
    g.toLinearMap.rTensor M x ∈ (Module.Grassmannian.map g N).toSubmodule := by
  let _ : Algebra A B := g.toAlgebra
  let _ : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq' (IsScalarTower.algebraMap_eq R A B)
  rw [Module.Grassmannian.map_toSubmodule]
  change Module.Grassmannian.baseChangeMkQ B N.toSubmodule
    (AlgebraTensorModule.rTensor R M (Algebra.linearMap A B) x) = 0
  rw [baseChangeMkQ_coefficient, Submodule.mkQ_apply,
    (Submodule.Quotient.mk_eq_zero _).mpr hx, tmul_zero]

omit [CommRing B] [Algebra R B] in
/-- Principal-local numerator membership clears a power in the original full relation. -/
theorem grassmannian_localized_numerator_iff
    (N : Module.Grassmannian A (A ⊗[R] M) d) (r : A) (x : A ⊗[R] M) :
    AlgebraTensorModule.rTensor R M (Algebra.linearMap A (Localization.Away r)) x ∈
      (Module.Grassmannian.map
        (IsScalarTower.toAlgHom R A (Localization.Away r)) N).toSubmodule ↔
      ∃ n : ℕ, r ^ n • x ∈ N.toSubmodule := by
  change _ ∈ (Module.Grassmannian.map
    (IsScalarTower.toAlgHom R A (Localization.Away r)) N).toSubmodule.restrictScalars A ↔ _
  rw [grassmannian_localized_relation]
  change _ ∈ N.toSubmodule.localized' (Localization.Away r) (.powers r) _ ↔ _
  rw [PrincipalSubmodulePatching.numerator_mem_iff]
  constructor
  · rintro ⟨⟨_, n, rfl⟩, hn⟩
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨⟨_, n, rfl⟩, hn⟩

end FLT.Mazur.GrassmannianChart
