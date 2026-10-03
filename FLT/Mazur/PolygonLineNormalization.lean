/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleLineTensorExact
public import FLT.Mazur.LineStructureProjection
public import FLT.Mazur.PolygonNormalizationExact
/-!
# Normalization with locally free line coefficients

Tensor the actual polygon normalization sequence and use the projection
formula to put its terms in line-section form. The inclusion is the pullback
unit; the difference retains the original zero-minus-adjacent-infinity
branches with a common target on the nodes. All positive polygon sizes,
including one and two, use the same construction.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonLineNormalization
open FCurve ModuleSheafTensor ModuleSheafTensorCurrying PolygonPinching
variable (K : Type u) [Field K] (n : ℕ) (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (L : C.left.Modules) (hL : LocallyFreeRankOne L)
/-- The original normalization complex tensored with the line. -/
def tensorComplex : ShortComplex C.left.Modules :=
  (PolygonNormalizationComplex.complex K n hn p q h).map (tensoring L)
include hL in
/-- The tensorized normalization complex is short exact. -/
lemma tensorComplex_shortExact [NeZero n] : (tensorComplex K n hn p q h L).ShortExact :=
  ModuleLineTensorExact.shortExact _ (PolygonNormalizationExact.shortExact K n hn p q h) L hL

/-- The normalization sequence with terms L, normalization pullback and node pullback. -/
def complex : ShortComplex C.left.Modules :=
  ShortComplex.mk
    ((leftUnitor L).inv ≫ (tensorComplex K n hn p q h L).f ≫
      (LineStructureProjection.iso p.left L hL).hom)
    ((LineStructureProjection.iso p.left L hL).inv ≫
      (tensorComplex K n hn p q h L).g ≫ (LineStructureProjection.iso q.left L hL).hom)
    (by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← Category.assoc (tensorComplex K n hn p q h L).f, ShortComplex.zero,
        zero_comp, comp_zero])
/-- Projection and the left unitor identify the tensorized and line-valued sequences. -/
def comparison : tensorComplex K n hn p q h L ≅ complex K n hn p q h L hL :=
  ShortComplex.isoMk (leftUnitor L) (LineStructureProjection.iso p.left L hL)
    (LineStructureProjection.iso q.left L hL)
    (by simp [complex]) (by simp [complex])
/-- The actual line-valued normalization sequence is short exact. -/
lemma shortExact [NeZero n] : (complex K n hn p q h L hL).ShortExact :=
  ShortComplex.shortExact_of_iso (comparison K n hn p q h L hL)
    (tensorComplex_shortExact K n hn p q h L hL)
/-- The first arrow is the normalization pullback adjunction unit. -/
lemma inclusion_eq_unit : (complex K n hn p q h L hL).f =
    (pullbackPushforwardAdjunction p.left).unit.app L := by
  change (leftUnitor L).inv ≫
    ModuleSheafTensor.map (StructureDirectImage.unitMap p.left) (𝟙 L) ≫
      (LineStructureProjection.iso p.left L hL).hom = _
  rw [LineStructureProjection.unit_compatibility, Iso.inv_hom_id_assoc]
/-- Either original branch restriction, with values in the same node line. -/
def branch (b : Bool) :
    (pushforward p.left).obj ((Scheme.Modules.pullback p.left).obj L) ⟶
      (pushforward q.left).obj ((Scheme.Modules.pullback q.left).obj L) :=
  (LineStructureProjection.iso p.left L hL).inv ≫
    (tensoring L).map (PolygonBranchDifferenceSheaf.branchRestriction K n hn p q h b) ≫
    (LineStructureProjection.iso q.left L hL).hom
/-- Projection intertwines each branch with its tensorized structure restriction. -/
lemma projection_branch (b : Bool) :
    (LineStructureProjection.iso p.left L hL).hom ≫ branch K n hn p q h L hL b =
      (tensoring L).map (PolygonBranchDifferenceSheaf.branchRestriction K n hn p q h b) ≫
        (LineStructureProjection.iso q.left L hL).hom := by
  simp only [branch, Iso.hom_inv_id_assoc]
/-- Each branch evaluates the function factor and retains the common line factor. -/
lemma branch_pure (b : Bool) (U : C.left.Opens)
    (r : Γ(StructureDirectImage.image p.left, U)) (l : Γ(L, U)) :
    (branch K n hn p q h L hL b).app U
      ((LineStructureProjection.iso p.left L hL).hom.app U
        (pure (StructureDirectImage.image p.left) L U r l)) =
    (LineStructureProjection.iso q.left L hL).hom.app U
      (pure (StructureDirectImage.image q.left) L U
        ((PolygonBranchDifferenceSheaf.branchRestriction K n hn p q h b).app U r) l) := by
  have he := congrArg (fun f ↦ f.app U (pure (StructureDirectImage.image p.left) L U r l))
    (projection_branch K n hn p q h L hL b)
  exact he.trans (congrArg ((LineStructureProjection.iso q.left L hL).hom.app U)
    (map_pure _ (𝟙 L) U r l))
/-- The second arrow is zero-branch value minus adjacent-infinity value. -/
lemma difference_eq_branches : (complex K n hn p q h L hL).g =
    branch K n hn p q h L hL false - branch K n hn p q h L hL true := by
  change (LineStructureProjection.iso p.left L hL).inv ≫
    (tensoring L).map (_ - _) ≫ (LineStructureProjection.iso q.left L hL).hom = _
  rw [Functor.map_sub, Preadditive.sub_comp, Preadditive.comp_sub]
  rfl
/-- A line section on the polygon has the same value on both branches. -/
lemma unit_branch (b : Bool) :
    (pullbackPushforwardAdjunction p.left).unit.app L ≫ branch K n hn p q h L hL b =
      (pullbackPushforwardAdjunction q.left).unit.app L := by
  rw [← inclusion_eq_unit K n hn p q h L hL]
  change ((leftUnitor L).inv ≫ (tensoring L).map
    (PolygonStructureInclusion.inclusion K n p) ≫ _) ≫ _ = _
  simp only [branch, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, PolygonBranchDifferenceSheaf.inclusion_branchRestriction]
  change (leftUnitor L).inv ≫
    ModuleSheafTensor.map (StructureDirectImage.unitMap q.left) (𝟙 L) ≫ _ = _
  rw [LineStructureProjection.unit_compatibility, Iso.inv_hom_id_assoc]
end FLT.Mazur.PolygonLineNormalization
