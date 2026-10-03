/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonStructureInclusion

/-!
# Branch difference on actual direct-image module sheaves

Restrict normalization functions to zero and to adjacent infinity at every
node. Their difference annihilates the polygon's structure-sheaf inclusion.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.StructureDirectImage
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Scheme.Modules PolygonStructureInclusion
variable {X Y Z : Scheme.{u}}
/-- Push the structure sheaf forward along a scheme morphism. -/
abbrev image (f : X ⟶ Y) : Y.Modules := (pushforward f).obj (structureModule X)
/-- Pull functions back along the scheme morphism. -/
def unitMap (f : X ⟶ Y) : structureModule Y ⟶ image f :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

theorem unitMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    unitMap g ≫ (pushforward g).map (unitMap f) ≫
      (pushforwardComp f g).hom.app (structureModule X) = unitMap (f ≫ g) := by
  ext U r
  rfl
/-- Restrict normalization functions along a map over the target. -/
def restriction (s : X ⟶ Y) (p : Y ⟶ Z) (q : X ⟶ Z) (w : s ≫ p = q) :
    image p ⟶ image q :=
  (pushforward p).map (unitMap s) ≫ (pushforwardComp s p).hom.app (structureModule X) ≫
    eqToHom (congrArg image w)
@[reassoc] theorem unitMap_restriction (s : X ⟶ Y) (p : Y ⟶ Z)
    (q : X ⟶ Z) (w : s ≫ p = q) :
    unitMap p ≫ restriction s p q w = unitMap q := by
  subst q
  simpa only [restriction, eqToHom_refl, Category.comp_id] using unitMap_comp s p
end FLT.Mazur.StructureDirectImage

namespace FLT.Mazur.PolygonBranchDifferenceSheaf
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Scheme.Modules PolygonPinching PolygonStructureInclusion StructureDirectImage
variable (K : Type u) [Field K] (n : ℕ) (hn : 0 < n)
variable {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
/-- Select either the zero branch or the adjacent infinity branch of every node. -/
def branchSection (b : Bool) : nodes K n ⟶ components K n :=
  Sigma.desc fun i ↦ endpoint K n hn i b
include h in
@[reassoc] theorem branchSection_normalization (b : Bool) :
    branchSection K n hn b ≫ p = q := by
  apply Sigma.hom_ext
  intro i
  have hw := congrArg (fun f ↦ branchι K n i b ≫ f) h.w
  simpa [branchSection, branchι, toComponents, toNodes, nodeι, Category.assoc] using hw
/-- The direct image of the structure sheaf of the nodes. -/
abbrev nodeModule : C.left.Modules := image q.left
/-- Restriction of normalization functions to one choice of branch over every node. -/
def branchRestriction (b : Bool) : normalizationModule K n p ⟶ nodeModule K n q :=
  restriction (branchSection K n hn b).left p.left q.left
    (congrArg Over.Hom.left (branchSection_normalization K n hn p q h b))
/-- Zero-branch value minus the adjacent infinity-branch value. -/
def difference : normalizationModule K n p ⟶ nodeModule K n q :=
  branchRestriction K n hn p q h false - branchRestriction K n hn p q h true
@[reassoc] theorem inclusion_branchRestriction (b : Bool) :
    inclusion K n p ≫ branchRestriction K n hn p q h b = unitMap q.left :=
  unitMap_restriction _ _ _ _
@[reassoc (attr := simp)] theorem inclusion_difference :
    inclusion K n p ≫ difference K n hn p q h = 0 := by
  rw [difference, Preadditive.comp_sub, inclusion_branchRestriction, inclusion_branchRestriction,
    sub_self]
end FLT.Mazur.PolygonBranchDifferenceSheaf
