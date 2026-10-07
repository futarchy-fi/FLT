/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineModulePullbackSections

/-!
# Maps from affine pulled-back coefficient sheaves

A scalar-extension map induces a sheaf map. Its effect on original sections
uses the actual pullback unit, and these sections determine the sheaf map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped ChangeOfRings

universe u

namespace FLT.Mazur.AffineTildePullbackMap

variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat R) (N : ModuleCat S)

/-- A scalar-extension map induces a map of the actual affine pullback sheaves. -/
def map (k : (ModuleCat.extendScalars φ.hom).obj M ⟶ N) :
    (pullback (Spec.map φ)).obj (tilde M) ⟶ tilde N :=
  ((AffineModulePullbackSections.tildePullbackIso φ).inv.app M) ≫
    (tilde.functor S).map k

/-- The induced map sends the original section to the prescribed unit-tensor image. -/
lemma map_unit (k : (ModuleCat.extendScalars φ.hom).obj M ⟶ N) (m : M) :
    (map φ M N k).app ⊤
        (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)).app ⊤
          (tilde.toOpen M ⊤ m)) =
      tilde.toOpen N ⊤ (k ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M m)) := by
  rw [← AffineModulePullbackSections.tildePullbackIso_unit]
  change ((tilde.functor S).map k).app ⊤
    (((AffineModulePullbackSections.tildePullbackIso φ).inv.app M).app ⊤
      (((AffineModulePullbackSections.tildePullbackIso φ).hom.app M).app ⊤ _)) = _
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.hom_inv_id_app,
    Hom.id_app, ConcreteCategory.id_apply]
  exact ConcreteCategory.congr_hom (tilde.toOpen_map_app k ⊤) _

/-- Original coefficient sections determine a morphism from the pulled-back tilde sheaf. -/
lemma hom_ext {P : (Spec S).Modules}
    (a b : (pullback (Spec.map φ)).obj (tilde M) ⟶ P)
    (h : ∀ m : M,
      a.app ⊤ (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)).app ⊤
        (tilde.toOpen M ⊤ m)) =
      b.app ⊤ (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)).app ⊤
        (tilde.toOpen M ⊤ m))) : a = b := by
  apply ((tilde.adjunction.comp (pullbackPushforwardAdjunction (Spec.map φ))).homEquiv
    M P).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact h

end FLT.Mazur.AffineTildePullbackMap
