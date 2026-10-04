/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonLineNormalization
public import FLT.Mazur.ModuleGlobalSectionPullback

/-!
# Geometric restriction into a common node line

The projection-defined polygon branches are actual pullback maps, followed
by composition and the node incidence equality. This applies to both
branches for every positive polygon size, including one and two.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LinePullbackRestriction
open FCurve ModuleSheafTensor ModuleSheafTensorCurrying StructureDirectImage
variable {X Y Z : Scheme.{u}}

/-- Pull back normalization sections along a branch and compose the pullbacks. -/
def restriction (s : X ⟶ Y) (p : Y ⟶ Z) (L : Z.Modules) :
    (pushforward p).obj ((pullback p).obj L) ⟶
      (pushforward (s ≫ p)).obj ((pullback (s ≫ p)).obj L) :=
  (pushforward p).map ((pullbackPushforwardAdjunction s).unit.app ((pullback p).obj L)) ≫
    (pushforwardComp s p).hom.app ((pullback s).obj ((pullback p).obj L)) ≫
    (pushforward (s ≫ p)).map ((pullbackComp s p).hom.app L)

/-- Geometric restriction evaluates the scalar and retains the pulled-back line factor. -/
lemma restriction_pure (s : X ⟶ Y) (p : Y ⟶ Z) (L : Z.Modules)
    (hL : LocallyFreeRankOne L) (U : Z.Opens)
    (r : Γ(Y, p ⁻¹ᵁ U)) (l : Γ(L, U)) :
    (restriction s p L).app U
      ((LineStructureProjection.iso p L hL).hom.app U (pure (image p) L U r l)) =
    (LineStructureProjection.iso (s ≫ p) L hL).hom.app U
      (pure (image (s ≫ p)) L U (s.app (p ⁻¹ᵁ U) r) l) := by
  rw [LineStructureProjection.iso_pure, LineStructureProjection.iso_pure]
  change ((pullbackComp s p).hom.app L).app _
    (((pullbackPushforwardAdjunction s).unit.app ((pullback p).obj L)).app _
      (r • (show Γ((pullback p).obj L, p ⁻¹ᵁ U) from
        ((pullbackPushforwardAdjunction p).unit.app L).app U l))) = _
  rw [Hom.app_smul]
  change ((pullbackComp s p).hom.app L).app _
    (s.app (p ⁻¹ᵁ U) r • (show Γ((pullback s).obj ((pullback p).obj L), s ⁻¹ᵁ (p ⁻¹ᵁ U)) from
      ((pullbackPushforwardAdjunction s).unit.app ((pullback p).obj L)).app _
        (((pullbackPushforwardAdjunction p).unit.app L).app U l))) = _
  rw [Hom.app_smul]
  congr 1
  rw [← modulePullbackComp_inv_unit]
  exact congrArg (fun k ↦ k.app _ (((pullbackPushforwardAdjunction (s ≫ p)).unit.app L).app U l))
    ((pullbackComp s p).inv_hom_id_app L)

/-- Projection intertwines geometric and tensorized structure restriction. -/
lemma projection_restriction (s : X ⟶ Y) (p : Y ⟶ Z) (L : Z.Modules)
    (hL : LocallyFreeRankOne L) :
    (LineStructureProjection.iso p L hL).hom ≫ restriction s p L =
      (tensoring L).map (StructureDirectImage.restriction s p (s ≫ p) rfl) ≫
        (LineStructureProjection.iso (s ≫ p) L hL).hom := by
  apply ModuleSheafTensor.hom_ext
  intro U r l
  change (restriction s p L).app U
      ((LineStructureProjection.iso p L hL).hom.app U (pure (image p) L U r l)) =
    (LineStructureProjection.iso (s ≫ p) L hL).hom.app U
      ((ModuleSheafTensor.map (StructureDirectImage.restriction s p (s ≫ p) rfl) (𝟙 L)).app U
        (pure (image p) L U r l))
  rw [ModuleSheafTensor.map_pure]
  exact restriction_pure s p L hL U r l

/-- Global geometric restriction is actual section pullback followed by composition. -/
lemma restriction_appTop (s : X ⟶ Y) (p : Y ⟶ Z) (L : Z.Modules)
    (t : Γ((pullback p).obj L, ⊤)) :
    (restriction s p L).app ⊤ t =
      ((pullbackComp s p).hom.app L).app ⊤ (pullGlobal s ((pullback p).obj L) t) := rfl
end FLT.Mazur.LinePullbackRestriction
namespace FLT.Mazur.LinePullbackRestriction
open FCurve ModuleSheafTensor ModuleSheafTensorCurrying StructureDirectImage
variable {X Y Z : Scheme.{u}}

/-- Geometric restriction with its target identified by a commuting triangle. -/
def along (s : X ⟶ Y) (p : Y ⟶ Z) (q : X ⟶ Z) (w : s ≫ p = q)
    (L : Z.Modules) :
    (pushforward p).obj ((pullback p).obj L) ⟶
      (pushforward q).obj ((pullback q).obj L) :=
  restriction s p L ≫ eqToHom (congrArg (fun f ↦ (pushforward f).obj ((pullback f).obj L)) w)

/-- The projection comparison respects a commuting triangle. -/
lemma projection_along (s : X ⟶ Y) (p : Y ⟶ Z) (q : X ⟶ Z) (w : s ≫ p = q)
    (L : Z.Modules) (hL : LocallyFreeRankOne L) :
    (LineStructureProjection.iso p L hL).hom ≫ along s p q w L =
      (tensoring L).map (StructureDirectImage.restriction s p q w) ≫
        (LineStructureProjection.iso q L hL).hom := by
  subst q
  simpa only [along, eqToHom_refl, Category.comp_id] using projection_restriction s p L hL
end FLT.Mazur.LinePullbackRestriction
namespace FLT.Mazur.PolygonLineNormalization
open FCurve PolygonPinching PolygonBranchDifferenceSheaf
variable (K : Type u) [Field K] (n : ℕ) (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (L : C.left.Modules) (hL : LocallyFreeRankOne L)

/-- Each normalization branch is the geometric pullback into the common node line. -/
lemma branch_eq_along (b : Bool) :
    branch K n hn p q h L hL b =
      LinePullbackRestriction.along (branchSection K n hn b).left p.left q.left
        (congrArg Over.Hom.left (branchSection_normalization K n hn p q h b)) L := by
  rw [← cancel_epi (LineStructureProjection.iso p.left L hL).hom, projection_branch,
    LinePullbackRestriction.projection_along]
  rfl
end FLT.Mazur.PolygonLineNormalization

namespace FLT.Mazur.StructureDirectImage
variable {W X Y Z : Scheme.{u}}
/-- Successive structure restrictions compose along the geometric triangle. -/
lemma restriction_comp (t : W ⟶ X) (s : X ⟶ Y) (p : Y ⟶ Z)
    (q : X ⟶ Z) (r : W ⟶ Z) (w : s ≫ p = q) (v : t ≫ q = r) :
    restriction s p q w ≫ restriction t q r v =
      restriction (t ≫ s) p r (by rw [Category.assoc, w, v]) := by
  subst q
  subst r
  ext U x
  rfl
end FLT.Mazur.StructureDirectImage
namespace FLT.Mazur.LinePullbackRestriction
open FCurve ModuleSheafTensor ModuleSheafTensorCurrying
variable {W X Y Z : Scheme.{u}}
/-- Successive line restrictions compose along the same geometric triangle. -/
lemma along_comp (t : W ⟶ X) (s : X ⟶ Y) (p : Y ⟶ Z)
    (q : X ⟶ Z) (r : W ⟶ Z) (w : s ≫ p = q) (v : t ≫ q = r)
    (L : Z.Modules) (hL : LocallyFreeRankOne L) :
    along s p q w L ≫ along t q r v L =
      along (t ≫ s) p r (by rw [Category.assoc, w, v]) L := by
  rw [← cancel_epi (LineStructureProjection.iso p L hL).hom,
    ← Category.assoc, projection_along, Category.assoc, projection_along,
    ← Functor.map_comp_assoc, StructureDirectImage.restriction_comp, projection_along]
end FLT.Mazur.LinePullbackRestriction

namespace FLT.Mazur.LinePullbackRestriction
open FCurve
private lemma along_congr {X Y Z : Scheme.{u}} {s t : X ⟶ Y} (hs : s = t)
    (p : Y ⟶ Z) (q : X ⟶ Z) (w : s ≫ p = q) (v : t ≫ p = q) (L : Z.Modules) :
    along s p q w L = along t p q v L := by
  subst t
  rfl
/-- Geometric line restrictions agree along two sides of a commuting square. -/
lemma along_square {V W X Y Z : Scheme.{u}}
    (t : W ⟶ X) (s : X ⟶ Y) (g : W ⟶ V) (f : V ⟶ Y)
    (p : Y ⟶ Z) (q : X ⟶ Z) (r : V ⟶ Z) (u : W ⟶ Z)
    (w : s ≫ p = q) (v : t ≫ q = u) (w' : f ≫ p = r) (v' : g ≫ r = u)
    (hs : t ≫ s = g ≫ f) (L : Z.Modules) (hL : LocallyFreeRankOne L) :
    along s p q w L ≫ along t q u v L = along f p r w' L ≫ along g r u v' L :=
  (along_comp t s p q u w v L hL).trans
    ((along_congr hs p u _ _ L).trans (along_comp g f p r u w' v' L hL).symm)
end FLT.Mazur.LinePullbackRestriction
