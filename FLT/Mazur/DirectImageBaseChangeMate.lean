/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemePullbackSquare
public import FLT.Mazur.ModuleGlobalSectionPullback
public import FLT.Mazur.SchemeModulePullbackUnits

/-!
# The actual direct-image base-change mate

The pullback square and the actual sheaf adjunctions construct the comparison
without any cohomological assumptions. Its counit equation and normalization
on pulled global sections are proved from the adjunction identities.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.DirectImageBaseChange
open FCurve SchemePullbackSquare
variable {P X T S : Scheme.{u}}
  (p : P ⟶ X) (q : P ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
  (w : q ≫ g = p ≫ f)

/-- The geometric square comparison preserves iterated global-section pullbacks. -/
lemma squareIso_unit (M : S.Modules) (s : Γ(M, ⊤)) :
    ((squareIso f q g p w).hom.app M).app ⊤
        (pullGlobal q _ (pullGlobal g M s)) =
      pullGlobal p _ (pullGlobal f M s) := by
  change ((pullbackComp p f).inv.app M).app ⊤
    (((pullbackCongr w).hom.app M).app ⊤
      (((pullbackComp q g).hom.app M).app ⊤
        (pullGlobal q _ (pullGlobal g M s)))) = _
  rw [pullGlobal_comp_hom]
  rw [show ((pullbackCongr w).hom.app M).app ⊤ (pullGlobal (q ≫ g) M s) =
    pullGlobal (p ≫ f) M s from SchemeModulePullbackUnits.congr_unit w M s]
  exact pullGlobal_comp p f M s

/-- The Beck-Chevalley map is the adjoint of the square followed by pulled counit. -/
def comparison (M : X.Modules) :
    (pullback g).obj ((pushforward f).obj M) ⟶
      (pushforward q).obj ((pullback p).obj M) :=
  ((pullbackPushforwardAdjunction q).homEquiv _ _)
    ((squareIso f q g p w).hom.app ((pushforward f).obj M) ≫
      (pullback p).map ((pullbackPushforwardAdjunction f).counit.app M))

/-- The actual comparison satisfies the counit mate equation. -/
@[reassoc]
lemma comparison_counit (M : X.Modules) :
    (pullback q).map (comparison p q f g w M) ≫
        (pullbackPushforwardAdjunction q).counit.app ((pullback p).obj M) =
      (squareIso f q g p w).hom.app ((pushforward f).obj M) ≫
        (pullback p).map ((pullbackPushforwardAdjunction f).counit.app M) :=
  ((pullbackPushforwardAdjunction q).homEquiv _ _).symm_apply_apply _

/-- A global section pulled from the old direct image becomes its total-space pullback. -/
lemma comparison_unit (M : X.Modules) (s : Γ(M, ⊤)) :
    (comparison p q f g w M).app ⊤
        (pullGlobal g ((pushforward f).obj M) s) = pullGlobal p M s := by
  change ((pullback p).map ((pullbackPushforwardAdjunction f).counit.app M)).app ⊤
    (((squareIso f q g p w).hom.app ((pushforward f).obj M)).app ⊤
      (pullGlobal q _ (pullGlobal g _ s))) = _
  rw [squareIso_unit]
  erw [pullGlobal_naturality]
  have ht := congrArg (fun k ↦ k.app ⊤ s)
    ((pullbackPushforwardAdjunction f).right_triangle_components M)
  change ((pullbackPushforwardAdjunction f).counit.app M).app ⊤
    (pullGlobal f ((pushforward f).obj M) s) = s at ht
  rw [ht]
  rfl

/-- The comparison commutes with arbitrary morphisms of the original coefficient sheaf. -/
@[reassoc]
lemma comparison_naturality {M N : X.Modules} (a : M ⟶ N) :
    (pullback g).map ((pushforward f).map a) ≫ comparison p q f g w N =
      comparison p q f g w M ≫ (pushforward q).map ((pullback p).map a) := by
  apply ((pullbackPushforwardAdjunction q).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm]
  simp only [comparison, Equiv.symm_apply_apply, ← Category.assoc]
  erw [(squareIso f q g p w).hom.naturality]
  simp only [Functor.comp_map, Category.assoc]
  rw [← Functor.map_comp]
  erw [(pullbackPushforwardAdjunction f).counit.naturality]
  simp only [Functor.id_map, Functor.map_comp]

end FLT.Mazur.DirectImageBaseChange
