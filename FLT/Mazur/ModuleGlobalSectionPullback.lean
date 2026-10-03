/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModulePullbackUnitCoherence
/-!
# Global sections under module pullback

The adjunction unit gives a semilinear map on global sections. It agrees with
the structure-module description of a section and respects composition. A
rank-one coordinate relation therefore remains valid on a common overlap.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y Z : Scheme.{u}}
/-- The semilinear pullback map on actual global sections. -/
def pullGlobal (f : X ⟶ Y) (M : Y.Modules) :
    Γ(M, ⊤) →ₛₗ[f.appTop.hom] Γ((pullback f).obj M, ⊤) :=
  { toFun := fun s ↦ ((pullbackPushforwardAdjunction f).unit.app M).app ⊤ s
    map_add' := by intros; exact map_add _ _ _
    map_smul' := by
      intro r s
      exact ((pullbackPushforwardAdjunction f).unit.app M).app_smul r s }
/-- Pulling back a section morphism agrees with the adjunction unit. -/
lemma pullGlobal_hom (f : X ⟶ Y) {M : Y.Modules}
    (s : structureModule Y ⟶ M) :
    pullGlobal f M (s.app ⊤ (1 : Γ(Y, ⊤))) =
      ((pullback f).map s).app ⊤
        ((modulePullbackUnitIso f).inv.app ⊤ (1 : Γ(X, ⊤))) := by
  have hu := modulePullbackUnitIso_unit f ⊤ (1 : Γ(Y, ⊤))
  simp only [map_one] at hu
  have hu' : ((pullbackPushforwardAdjunction f).unit.app (structureModule Y)).app ⊤
      (1 : Γ(Y, ⊤)) = (modulePullbackUnitIso f).inv.app ⊤ (1 : Γ(X, ⊤)) := by
    rw [← hu]
    exact (congrArg (fun k ↦ k.app ⊤
      (((pullbackPushforwardAdjunction f).unit.app (structureModule Y)).app ⊤
        (1 : Γ(Y, ⊤)))) (modulePullbackUnitIso f).hom_inv_id).symm
  have hn := congrArg (fun k ↦ k.app ⊤ (1 : Γ(Y, ⊤)))
    ((pullbackPushforwardAdjunction f).unit.naturality s).symm
  change ((pullback f).map s).app ⊤ _ = pullGlobal f M _ at hn
  exact hn.symm.trans (congrArg (((pullback f).map s).app ⊤) hu')
/-- Two successive section pullbacks agree with the composition comparison. -/
lemma pullGlobal_comp (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (s : Γ(M, ⊤)) :
    ((pullbackComp f g).inv.app M).app ⊤ (pullGlobal (f ≫ g) M s) =
      pullGlobal f ((pullback g).obj M) (pullGlobal g M s) :=
  modulePullbackComp_inv_unit f g M ⊤ s
/-- Pullback of sections is natural in the module sheaf. -/
lemma pullGlobal_naturality (f : X ⟶ Y) {M N : Y.Modules} (e : M ⟶ N)
    (s : Γ(M, ⊤)) :
    ((pullback f).map e).app ⊤ (pullGlobal f M s) =
      pullGlobal f N (e.app ⊤ s) := by
  exact congrArg (fun k ↦ k.app ⊤ s)
    ((pullbackPushforwardAdjunction f).unit.naturality e).symm

/-- The forward composition comparison identifies successive section pullbacks. -/
lemma pullGlobal_comp_hom (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (s : Γ(M, ⊤)) :
    ((pullbackComp f g).hom.app M).app ⊤
      (pullGlobal f ((pullback g).obj M) (pullGlobal g M s)) =
        pullGlobal (f ≫ g) M s := by
  rw [← pullGlobal_comp]
  exact congrArg (fun k ↦ k.app ⊤ (pullGlobal (f ≫ g) M s))
    ((pullbackComp f g).inv_hom_id_app M)

/-- A rank-one coordinate relation persists after pullback to an overlap. -/
lemma pullGlobal_coordinate_relation (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (e : Γ((pullback g).obj M, ⊤) ≃ₗ[Γ(Y, ⊤)] Γ(Y, ⊤))
    (c s : Γ(M, ⊤)) :
    f.appTop (e (pullGlobal g M c)) • pullGlobal (f ≫ g) M s =
      f.appTop (e (pullGlobal g M s)) • pullGlobal (f ≫ g) M c := by
  have h : e (pullGlobal g M c) • pullGlobal g M s =
      e (pullGlobal g M s) • pullGlobal g M c := by
    apply e.injective
    rw [e.map_smul, e.map_smul]
    exact mul_comm _ _
  have h' := congrArg (fun t ↦ ((pullbackComp f g).hom.app M).app ⊤
    (pullGlobal f ((pullback g).obj M) t)) h
  simpa only [map_smulₛₗ, Hom.app_smul, pullGlobal_comp_hom] using h'
end FLT.Mazur.FCurve
