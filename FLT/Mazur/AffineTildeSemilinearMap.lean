/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTildePullbackMap

/-!
# Sheaf maps induced by original semilinear coefficient maps

No localization hypothesis is needed to construct the map. Its normalization
on original sections makes it unique and identifies any scalar-extension isomorphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.AffineTildeSemilinearMap

variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat R) (N : ModuleCat S)

/-- The actual sheaf map induced by a semilinear coefficient map. -/
def map (g : M ⟶ (ModuleCat.restrictScalars φ.hom).obj N) :
    (pullback (Spec.map φ)).obj (tilde M) ⟶ tilde N :=
  AffineTildePullbackMap.map φ M N
    (((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv M N).symm g)

/-- On original sections the sheaf map is exactly the supplied coefficient map. -/
lemma map_unit (g : M ⟶ (ModuleCat.restrictScalars φ.hom).obj N) (m : M) :
    (map φ M N g).app ⊤
        (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)).app ⊤
          (tilde.toOpen M ⊤ m)) = tilde.toOpen N ⊤ (g m) := by
  have h := AffineTildePullbackMap.map_unit φ M N
    (((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv M N).symm g) m
  exact h.trans (congrArg (tilde.toOpen N ⊤)
    (ConcreteCategory.congr_hom
      (((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv M N).apply_symm_apply g) m))

/-- A normalized sheaf map agrees with the map constructed from its coefficient map. -/
lemma map_unique (g : M ⟶ (ModuleCat.restrictScalars φ.hom).obj N)
    (a : (pullback (Spec.map φ)).obj (tilde M) ⟶ tilde N)
    (h : ∀ m : M, a.app ⊤
      (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)).app ⊤
        (tilde.toOpen M ⊤ m)) = tilde.toOpen N ⊤ (g m)) : a = map φ M N g := by
  apply AffineTildePullbackMap.hom_ext
  intro m
  exact (h m).trans (map_unit φ M N g m).symm

end FLT.Mazur.AffineTildeSemilinearMap
