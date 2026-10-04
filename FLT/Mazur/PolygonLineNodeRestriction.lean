/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SealedLineRestriction
public import FLT.Mazur.PolygonNodeIncidence

/-!
# Component factorizations of the normalization branches

Both original branches factor through their components into the same node line.
Sealed restrictions prevent conversion from expanding the geometric adjunctions.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonLineNodeRestriction
open FCurve PolygonPinching PolygonBranchDifferenceSheaf LinePullbackRestriction
variable (K : Type u) [Field K] (n : ℕ) (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (L : C.left.Modules) (hL : LocallyFreeRankOne L)

/-- The original normalization branch is the sealed geometric restriction. -/
lemma branch_eq_sealed (b : Bool) :
    PolygonLineNormalization.branch K n hn p q h L hL b =
      sealedAlong (branchSection K n hn b).left p.left q.left
        (congrArg Over.Hom.left (branchSection_normalization K n hn p q h b)) L :=
  (PolygonLineNormalization.branch_eq_along K n hn p q h L hL b).trans
    (sealedAlong_def _ _ _ _ L).symm

/-- The zero branch at node i passes through component i. -/
lemma zero_endpoint (i : Fin n) :
    (nodeι K n i).left ≫ (branchSection K n hn false).left =
      ProjectiveLine.zero K ≫ (componentι K n i).left := by
  change (nodeι K n i ≫ branchSection K n hn false).left = _
  simp only [nodeι, branchSection, Sigma.ι_comp_desc]
  rfl

include hL in
/-- The zero square factors geometric restriction through its component. -/
lemma zero_geometric (i : Fin n) :
    sealedAlong (branchSection K n hn false).left p.left q.left
      (congrArg Over.Hom.left (branchSection_normalization K n hn p q h false)) L ≫
      sealedAlong (nodeι K n i).left q.left (nodeι K n i ≫ q).left rfl L =
    sealedAlong (componentι K n i).left p.left (componentι K n i ≫ p).left rfl L ≫
      sealedAlong (ProjectiveLine.zero K) (componentι K n i ≫ p).left (nodeι K n i ≫ q).left
        (congrArg Over.Hom.left (PolygonNodeIncidence.zero_node K n hn p q h i)) L :=
  sealedAlong_square _ _ _ _ _ _ _ _ _ _ _ _ (zero_endpoint K n hn i) L hL

/-- The actual zero branch factors through component restriction and evaluation. -/
lemma zero_branch (i : Fin n) :
    PolygonLineNormalization.branch K n hn p q h L hL false ≫
      sealedAlong (nodeι K n i).left q.left (nodeι K n i ≫ q).left rfl L =
    sealedAlong (componentι K n i).left p.left (componentι K n i ≫ p).left rfl L ≫
      sealedAlong (ProjectiveLine.zero K) (componentι K n i ≫ p).left (nodeι K n i ≫ q).left
        (congrArg Over.Hom.left (PolygonNodeIncidence.zero_node K n hn p q h i)) L :=
  (congrArg (fun f ↦ f ≫
    sealedAlong (nodeι K n i).left q.left (nodeι K n i ≫ q).left rfl L)
    (branch_eq_sealed K n hn p q h L hL false)).trans
      (zero_geometric K n hn p q h L hL i)

/-- The infinity branch at node i passes through the next component. -/
lemma infinity_endpoint (i : Fin n) :
    (nodeι K n i).left ≫ (branchSection K n hn true).left =
      ProjectiveLine.infinity K ≫ (componentι K n (next hn i)).left := by
  change (nodeι K n i ≫ branchSection K n hn true).left = _
  simp only [nodeι, branchSection, Sigma.ι_comp_desc]
  rfl

include hL in
/-- The infinity square factors geometric restriction through the next component. -/
lemma infinity_geometric (i : Fin n) :
    sealedAlong (branchSection K n hn true).left p.left q.left
      (congrArg Over.Hom.left (branchSection_normalization K n hn p q h true)) L ≫
      sealedAlong (nodeι K n i).left q.left (nodeι K n i ≫ q).left rfl L =
    sealedAlong (componentι K n (next hn i)).left p.left
      (componentι K n (next hn i) ≫ p).left rfl L ≫
      sealedAlong (ProjectiveLine.infinity K) (componentι K n (next hn i) ≫ p).left
        (nodeι K n i ≫ q).left
        (congrArg Over.Hom.left (PolygonNodeIncidence.infinity_node K n hn p q h i)) L :=
  sealedAlong_square _ _ _ _ _ _ _ _ _ _ _ _ (infinity_endpoint K n hn i) L hL

/-- The actual infinity branch factors through the adjacent component endpoint. -/
lemma infinity_branch (i : Fin n) :
    PolygonLineNormalization.branch K n hn p q h L hL true ≫
      sealedAlong (nodeι K n i).left q.left (nodeι K n i ≫ q).left rfl L =
    sealedAlong (componentι K n (next hn i)).left p.left
      (componentι K n (next hn i) ≫ p).left rfl L ≫
      sealedAlong (ProjectiveLine.infinity K) (componentι K n (next hn i) ≫ p).left
        (nodeι K n i ≫ q).left
        (congrArg Over.Hom.left (PolygonNodeIncidence.infinity_node K n hn p q h i)) L :=
  (congrArg (fun f ↦ f ≫
    sealedAlong (nodeι K n i).left q.left (nodeι K n i ≫ q).left rfl L)
    (branch_eq_sealed K n hn p q h L hL true)).trans
      (infinity_geometric K n hn p q h L hL i)

end FLT.Mazur.PolygonLineNodeRestriction
