/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

import all Mathlib.RingTheory.Grassmannian

public import FLT.Mazur.GrassmannianQuotientSheaf
public import FLT.Mazur.AffineModulePullbackSections

/-!
# Base change of the original Grassmannian quotient sheaf

For every coefficient algebra map, the actual functor-image quotient sheaf is
isomorphic to the pullback of the original quotient. The isomorphism retains
the ambient quotient projection; no flatness assumption is needed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A B M : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [AddCommGroup M] [Module R M] {d : ℕ}
variable (f : A →ₐ[R] B) (N : Module.Grassmannian A (A ⊗[R] M) d)

/-- The actual functor-image quotient is the tensor extension of the full quotient. -/
def grassmannianQuotientBaseChangeEquiv :
    let _ := f.toAlgebra
    ((B ⊗[R] M) ⧸ (Module.Grassmannian.map f N).toSubmodule) ≃ₗ[B]
      B ⊗[A] ((A ⊗[R] M) ⧸ N.toSubmodule) := by
  let _ := f.toAlgebra
  let _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq'
    (IsScalarTower.algebraMap_eq R A B)
  exact (Submodule.quotEquivOfEq _ _ (Module.Grassmannian.map_toSubmodule f N)).trans
    (Module.Grassmannian.baseChangeMkQEquiv N.toSubmodule)

/-- The ambient tensor sheaf also commutes with arbitrary coefficient pullback. -/
def grassmannianAmbientSheafPullbackIso :
    (pullback (Spec.map (CommRingCat.ofHom f.toRingHom))).obj
      (tilde (ModuleCat.of A (A ⊗[R] M))) ≅ tilde (ModuleCat.of B (B ⊗[R] M)) := by
  let _ := f.toAlgebra
  let _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq'
    (IsScalarTower.algebraMap_eq R A B)
  exact (AffineModulePullbackSections.tildePullbackIso
    (CommRingCat.ofHom f.toRingHom)).symm.app _ ≪≫
      (tilde.functor (.of B)).mapIso
        (AlgebraTensorModule.cancelBaseChange R A B B M).toModuleIso

/-- Pullback is the quotient sheaf of the actual Grassmannian functor image. -/
def grassmannianQuotientSheafPullbackIso :
    (pullback (Spec.map (CommRingCat.ofHom f.toRingHom))).obj
      (grassmannianQuotientSheaf N) ≅
        grassmannianQuotientSheaf (Module.Grassmannian.map f N) := by
  let _ := f.toAlgebra
  exact (AffineModulePullbackSections.tildePullbackIso
    (CommRingCat.ofHom f.toRingHom)).symm.app _ ≪≫
      (tilde.functor (.of B)).mapIso
        (grassmannianQuotientBaseChangeEquiv f N).symm.toModuleIso

/-- The tensor quotient comparison preserves every ambient numerator. -/
theorem grassmannianQuotientBaseChangeEquiv_mk (x : B ⊗[R] M) :
    let _ := f.toAlgebra
    let _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq'
      (IsScalarTower.algebraMap_eq R A B)
    grassmannianQuotientBaseChangeEquiv f N
      ((Module.Grassmannian.map f N).toSubmodule.mkQ x) =
        Module.Grassmannian.baseChangeMkQ B N.toSubmodule x := by
  let _ := f.toAlgebra
  let _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq'
    (IsScalarTower.algebraMap_eq R A B)
  simp only [grassmannianQuotientBaseChangeEquiv, LinearEquiv.trans_apply,
    Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk,
    Module.Grassmannian.baseChangeMkQEquiv,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The quotient comparison commutes with the scalar extension of the original projection. -/
theorem grassmannianQuotientBaseChangeEquiv_projection :
    let _ := f.toAlgebra
    let _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq'
      (IsScalarTower.algebraMap_eq R A B)
    (grassmannianQuotientBaseChangeEquiv f N).symm.toLinearMap.comp
      (N.toSubmodule.mkQ.baseChange B) =
        (Module.Grassmannian.map f N).toSubmodule.mkQ.comp
          (AlgebraTensorModule.cancelBaseChange R A B B M).toLinearMap := by
  let _ := f.toAlgebra
  let _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq'
    (IsScalarTower.algebraMap_eq R A B)
  apply LinearMap.ext
  intro x
  apply (grassmannianQuotientBaseChangeEquiv f N).injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [grassmannianQuotientBaseChangeEquiv_mk]
  simp only [Module.Grassmannian.baseChangeMkQ, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

/-- The actual sheaf pullback comparison retains the original ambient quotient map. -/
@[reassoc] theorem grassmannianQuotientSheafPullbackIso_projection :
    (pullback (Spec.map (CommRingCat.ofHom f.toRingHom))).map
        (grassmannianQuotientSheafMap N) ≫ (grassmannianQuotientSheafPullbackIso f N).hom =
      (grassmannianAmbientSheafPullbackIso (M := M) f).hom ≫
        grassmannianQuotientSheafMap (Module.Grassmannian.map f N) := by
  let _ := f.toAlgebra
  let _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq'
    (IsScalarTower.algebraMap_eq R A B)
  have hn := (AffineModulePullbackSections.tildePullbackIso
    (CommRingCat.ofHom f.toRingHom)).inv.naturality (ModuleCat.ofHom N.toSubmodule.mkQ)
  dsimp only [grassmannianQuotientSheaf] at *
  dsimp only [grassmannianQuotientSheafPullbackIso, grassmannianAmbientSheafPullbackIso,
    grassmannianQuotientSheafMap, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_inv, Iso.app_hom]
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
    Category.assoc, ← Functor.map_comp]
  congr 2
  exact ModuleCat.hom_ext (grassmannianQuotientBaseChangeEquiv_projection f N)

end FLT.Mazur.GrassmannianChart
