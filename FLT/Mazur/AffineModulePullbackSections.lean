/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Pullback of affine quasi-coherent module sheaves

The sheaf pullback of a tilde module is the tilde of scalar extension. The
comparison comes from the actual sheaf pullback adjunction, by uniqueness of
left adjoints to restriction of scalars on global sections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
open scoped ChangeOfRings
universe u
namespace FLT.Mazur.AffineModulePullbackSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- Pushforward on affine global sections is naturally restriction of scalars. -/
def pushforwardSectionsIso :
    pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor ≅
      moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom :=
  NatIso.ofComponents (fun M ↦
    (TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
      (evaluation _ _).obj (op ⊤)).mapIso
        ((pushforwardCompModulesSpecToSheafIso φ).app M)) (by
    intro M N f
    exact congrArg (fun g ↦ g.1.app (op ⊤))
      ((pushforwardCompModulesSpecToSheafIso φ).hom.naturality f))

/-- Scalar extension followed by tilde has the same right adjoint as sheaf pullback
following tilde. -/
def scalarTildeAdjunction :
    ModuleCat.extendScalars φ.hom ⋙ tilde.functor S ⊣
      pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor :=
  ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp tilde.adjunction).ofNatIsoRight
    (pushforwardSectionsIso φ).symm

/-- Pulling back the actual tilde sheaf agrees with scalar extension followed by tilde. -/
def tildePullbackIso :
    ModuleCat.extendScalars φ.hom ⋙ tilde.functor S ≅
      tilde.functor R ⋙ pullback (Spec.map φ) :=
  (scalarTildeAdjunction φ).leftAdjointUniq
    (tilde.adjunction.comp (pullbackPushforwardAdjunction (Spec.map φ)))

/-- Affine quasi-coherent pullback is reconstructed from the scalar-extended sections. -/
def pullbackIso (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (tilde.functor S).obj ((ModuleCat.extendScalars φ.hom).obj
      (moduleSpecΓFunctor.obj M)) ≅ (pullback (Spec.map φ)).obj M :=
  (tildePullbackIso φ).app (moduleSpecΓFunctor.obj M) ≪≫
    (pullback (Spec.map φ)).mapIso (asIso M.fromTildeΓ)

/-- Global sections of the actual affine quasi-coherent pullback are scalar extension. -/
def sectionsIso (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj M) ≅
      moduleSpecΓFunctor.obj ((pullback (Spec.map φ)).obj M) :=
  (tilde.toTildeΓNatIso.app _) ≪≫ moduleSpecΓFunctor.mapIso (pullbackIso φ M)

/-- The affine pushforward comparison acts as the identity on global sections. -/
lemma pushforwardSectionsIso_hom_apply (M : (Spec S).Modules)
    (m : moduleSpecΓFunctor.obj ((pushforward (Spec.map φ)).obj M)) :
    (pushforwardSectionsIso φ).hom.app M m = m := rfl

/-- The inverse pushforward comparison also acts as the identity. -/
lemma pushforwardSectionsIso_inv_apply (M : (Spec S).Modules)
    (m : (ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj M)) :
    (pushforwardSectionsIso φ).inv.app M m = m := rfl

/-- On coefficients, the tilde comparison is the sheaf pullback adjunction unit. -/
lemma tildePullbackIso_unit (N : ModuleCat R) (n : N) :
    ((tildePullbackIso φ).hom.app N).app ⊤
      (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj N) ⊤
        ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app N n)) =
    ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde N)).app ⊤
      (tilde.toOpen N ⊤ n) := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app (scalarTildeAdjunction φ)
    (tilde.adjunction.comp (pullbackPushforwardAdjunction (Spec.map φ))) N
  rw [scalarTildeAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.comp_homEquiv, Adjunction.comp_unit_app] at h
  exact congrArg (fun k ↦ k n) h

/-- The section isomorphism sends a unit tensor to the actual pullback section. -/
lemma sectionsIso_unit (M : (Spec R).Modules) [M.IsQuasicoherent]
    (m : moduleSpecΓFunctor.obj M) :
    (sectionsIso φ M).hom ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app _ m) =
      ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤ m := by
  change ((pullback (Spec.map φ)).map M.fromTildeΓ).app ⊤
    (((tildePullbackIso φ).hom.app _).app ⊤
      (tilde.toOpen _ ⊤ ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app _ m))) = _
  rw [tildePullbackIso_unit]
  have h := congrArg (fun k ↦ k.app ⊤ (tilde.toOpen _ ⊤ m))
    ((pullbackPushforwardAdjunction (Spec.map φ)).unit.naturality M.fromTildeΓ)
  change _ = ((pullback (Spec.map φ)).map M.fromTildeΓ).app ⊤ _ at h
  erw [← h]
  have ht := congrArg (fun k ↦ k m) (tilde.adjunction.right_triangle_components M)
  change M.fromTildeΓ.app ⊤ (tilde.toOpen _ ⊤ m) = m at ht
  exact congrArg (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤) ht

/-- On pure tensors the section isomorphism multiplies the pulled-back section. -/
lemma sectionsIso_tmul (M : (Spec R).Modules) [M.IsQuasicoherent]
    (s : S) (m : moduleSpecΓFunctor.obj M) :
    (sectionsIso φ M).hom (s ⊗ₜ[R,φ.hom] m) =
      s • (show moduleSpecΓFunctor.obj ((pullback (Spec.map φ)).obj M) from
        ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤ m) := by
  have h := (sectionsIso φ M).hom.hom.map_smul s
    (show (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj M) from (1 : S) ⊗ₜ[R,φ.hom] m)
  have ht : s • ((1 : S) ⊗ₜ[R,φ.hom] m : (ModuleCat.extendScalars φ.hom).obj
      (moduleSpecΓFunctor.obj M)) = s ⊗ₜ[R,φ.hom] m := by
    exact (ModuleCat.ExtendScalars.smul_tmul φ.hom s 1 m).trans
      (congrArg (fun a : S ↦ a ⊗ₜ[R,φ.hom] m) (mul_one s))
  calc
    _ = s • (sectionsIso φ M).hom ((1 : S) ⊗ₜ[R,φ.hom] m) :=
      (congrArg (sectionsIso φ M).hom ht).symm.trans h
    _ = _ := congrArg (fun n : moduleSpecΓFunctor.obj ((pullback (Spec.map φ)).obj M) ↦ s • n)
      (sectionsIso_unit φ M m)

/-- Pullback between spectra preserves quasi-coherence. -/
theorem isQuasicoherent_pullback (M : (Spec R).Modules) [M.IsQuasicoherent] :
    ((pullback (Spec.map φ)).obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).prop_of_iso
    (pullbackIso φ M) inferInstance

end FLT.Mazur.AffineModulePullbackSections
