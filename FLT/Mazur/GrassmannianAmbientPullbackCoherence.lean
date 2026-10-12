/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianQuotientBaseChange
public import FLT.Mazur.AffineTildeMorphismCoherence

/-!
# Coherence of the original Grassmannian ambient sheaf

The ambient pullback comparison sends every original tensor to its coefficient
image. This normalization proves compatibility with successive refinements.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
open AffineTildePullbackSectionMap AffineIteratedPullbackSections
universe u
variable {R A B C M : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C] [AddCommGroup M] [Module R M]
variable (f : A →ₐ[R] B)

/-- Cancellation of a unit tensor is the original coefficient map on ambient numerators. -/
theorem grassmannianAmbientBaseChange_unit (x : A ⊗[R] M) :
    let _ := f.toAlgebra
    let _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq'
      (IsScalarTower.algebraMap_eq R A B)
    AlgebraTensorModule.cancelBaseChange R A B B M ((1 : B) ⊗ₜ[A] x) =
      LinearMap.rTensor M f.toLinearMap x := by
  let _ := f.toAlgebra
  let _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq'
    (IsScalarTower.algebraMap_eq R A B)
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  | tmul a m =>
    simp only [AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.rTensor_tmul,
      AlgHom.toLinearMap_apply]
    simp only [Algebra.smul_def, mul_one]
    rfl

/-- The actual ambient sheaf comparison acts by coefficient transport on original sections. -/
theorem grassmannianAmbientSheafPullbackIso_unit (x : A ⊗[R] M) :
    moduleSpecΓFunctor.map (grassmannianAmbientSheafPullbackIso (M := M) f).hom
      (unit (CommRingCat.ofHom f.toRingHom) (ModuleCat.of A (A ⊗[R] M)) x) =
        (tilde.toTildeΓNatIso (R := .of B)).hom.app (ModuleCat.of B (B ⊗[R] M))
          (LinearMap.rTensor M f.toLinearMap x) := by
  let _ := f.toAlgebra
  let _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq'
    (IsScalarTower.algebraMap_eq R A B)
  have h := AffineTildePullbackSectionMap.map_unit (CommRingCat.ofHom f.toRingHom)
    (ModuleCat.of A (A ⊗[R] M)) (ModuleCat.of B (B ⊗[R] M))
    (AlgebraTensorModule.cancelBaseChange R A B B M).toModuleIso.hom x
  exact h.trans (congrArg
    ((tilde.toTildeΓNatIso (R := .of B)).hom.app (ModuleCat.of B (B ⊗[R] M)))
      (grassmannianAmbientBaseChange_unit f x))

/-- Coefficient transport on ambient tensors composes without changing the original module. -/
theorem grassmannianAmbientCoefficient_comp (g : B →ₐ[R] C) (x : A ⊗[R] M) :
    LinearMap.rTensor M g.toLinearMap (LinearMap.rTensor M f.toLinearMap x) =
      LinearMap.rTensor M (g.comp f).toLinearMap x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

attribute [local irreducible] grassmannianAmbientSheafPullbackIso compositeIso
attribute [local irreducible] Scheme.Modules.pullback

/-- Successive coefficient pullbacks agree with direct ambient pullback. -/
theorem grassmannianAmbientSheafPullbackIso_comp (g : B →ₐ[R] C)
    (w : Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      Spec.map (CommRingCat.ofHom f.toRingHom) =
        Spec.map (CommRingCat.ofHom (g.comp f).toRingHom)) :
    (compositeIso (Spec.map (CommRingCat.ofHom g.toRingHom))
      (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom (g.comp f).toRingHom)) w
      (tilde (ModuleCat.of A (A ⊗[R] M)))).inv ≫
        (pullback (Spec.map (CommRingCat.ofHom g.toRingHom))).map
          (grassmannianAmbientSheafPullbackIso (M := M) f).hom ≫
        (grassmannianAmbientSheafPullbackIso (M := M) g).hom =
      (grassmannianAmbientSheafPullbackIso (M := M) (g.comp f)).hom := by
  exact AffineTildeMorphismCoherence.hom_comp
    (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom g.toRingHom)
    (CommRingCat.ofHom (g.comp f).toRingHom) w
    (ModuleCat.of A (A ⊗[R] M)) (ModuleCat.of B (B ⊗[R] M))
    (ModuleCat.of C (C ⊗[R] M))
    _ _ _ (LinearMap.rTensor M f.toLinearMap) (LinearMap.rTensor M g.toLinearMap)
      (LinearMap.rTensor M (g.comp f).toLinearMap)
      (grassmannianAmbientSheafPullbackIso_unit f)
      (grassmannianAmbientSheafPullbackIso_unit g)
      (grassmannianAmbientSheafPullbackIso_unit (g.comp f))
      (grassmannianAmbientCoefficient_comp f g)

end FLT.Mazur.GrassmannianChart
