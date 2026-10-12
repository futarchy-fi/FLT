/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

import all Mathlib.RingTheory.Grassmannian

public import FLT.Mazur.GrassmannianFunctorLocalizedChart
public import Mathlib.RingTheory.LocalProperties.Submodule

/-!
# The original Grassmannian relation under principal localization

The functor's tensor quotient kernel is exactly the localization of its original
relation. Equality of these actual localized functor points detects global equality.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A B M : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [AddCommGroup M] [Module R M] {d : ℕ}

/-- The tensor quotient map on the coefficient extension of any original vector. -/
theorem baseChangeMkQ_coefficient (N : Submodule A (A ⊗[R] M)) (x : A ⊗[R] M) :
    Module.Grassmannian.baseChangeMkQ B N
      (AlgebraTensorModule.rTensor R M (Algebra.linearMap A B) x) =
        (1 : B) ⊗ₜ[A] N.mkQ x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    simp only [AlgebraTensorModule.rTensor_tmul, Algebra.linearMap_apply,
      Module.Grassmannian.baseChangeMkQ, LinearMap.comp_apply, LinearEquiv.coe_coe,
      AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul]
    have ht : a ⊗ₜ[R] m = a • ((1 : A) ⊗ₜ[R] m) := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    rw [ht, map_smul, tmul_smul, smul_tmul', Algebra.smul_def, mul_one]
  | add x y hx hy => simp only [map_add, tmul_add, hx, hy]

/-- With the existing coefficient algebra structure, the functor relation is its tensor kernel. -/
theorem grassmannian_map_tower_relation (N : Module.Grassmannian A (A ⊗[R] M) d) :
    (Module.Grassmannian.map (IsScalarTower.toAlgHom R A B) N).toSubmodule =
      (Module.Grassmannian.baseChangeMkQ B N.toSubmodule).ker := by
  have ha : (IsScalarTower.toAlgHom R A B).toAlgebra = ‹Algebra A B› :=
    Algebra.algebra_ext _ _ fun _ ↦ rfl
  exact (Module.Grassmannian.map_toSubmodule (IsScalarTower.toAlgHom R A B) N).trans
    (baseChangeMkQ_ker_algebra_congr _ _ ha _ _ N.toSubmodule)

omit [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B] in
/-- The complete original relation localizes to the complete functor relation. -/
theorem grassmannian_localized_relation (N : Module.Grassmannian A (A ⊗[R] M) d)
    (r : A) :
    (Module.Grassmannian.map
      (IsScalarTower.toAlgHom R A (Localization.Away r)) N).toSubmodule.restrictScalars A =
        N.toSubmodule.localized₀ (.powers r)
          (AlgebraTensorModule.rTensor R M (Algebra.linearMap A (Localization.Away r))) := by
  let f := AlgebraTensorModule.rTensor R M (Algebra.linearMap A (Localization.Away r))
  let g := TensorProduct.mk A (Localization.Away r) ((A ⊗[R] M) ⧸ N.toSubmodule) 1
  have he : (Module.Grassmannian.baseChangeMkQ (Localization.Away r)
      N.toSubmodule).restrictScalars A = IsLocalizedModule.map (.powers r) f g
        N.toSubmodule.mkQ := by
    apply IsLocalizedModule.linearMap_ext (.powers r) f g
    apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      baseChangeMkQ_coefficient, LinearMap.comp_apply, IsLocalizedModule.map_apply]
    rfl
  rw [grassmannian_map_tower_relation]
  change ((Module.Grassmannian.baseChangeMkQ (Localization.Away r)
    N.toSubmodule).restrictScalars A).ker = _
  rw [he, LinearMap.ker_localizedMap_eq_localized₀_ker, Submodule.ker_mkQ]

end FLT.Mazur.GrassmannianChart
