/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedLaurentEdges
public import FLT.Mazur.PolygonInfinitesimalEdgeExt
public import FLT.Mazur.PolygonCyclicSeparated

/-!
# The original universal action on the entire closed Laurent family

The full Laurent edges determine maps to the separated original polygon.
Thus the comparison retains all original nodes as well as both Laurent coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open CartesianMonoidalCategory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "U" => MultiplicativeGroupScheme.gm K
local notation "C" => PolygonCyclicAtlas.polygon K n h
local notation "P" => PolygonCyclicAtlas.normalization K n h
local notation "Q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn
local notation "e" => completeClosedLaurentProductIso K n h
local notation "z" => zeroFiberIso K n h
local notation "E" => edge K[T;T⁻¹] (LaurentPolynomial.C (0 : K)) n h
local notation "act" => PolygonUniversalAction.act K n hn P Q hp

/-- Original full normalization tori retain the original closed rotation. -/
@[reassoc] theorem completeClosedOriginalTorus_rotation (a : ZMod n) (i : Fin n) :
    (torusToComponent K ≫ componentι K n i ≫ P).left ≫
        PolygonCyclicAtlas.closedRotation K n h a =
      (torusToComponent K ≫ componentι K n (rotateIndex a i) ≫ P).left := by
  rw [originalTorus_eq_closedEdge, Category.assoc, PolygonCyclicAtlas.chart_closedRotation,
    originalTorus_eq_closedEdge]

/-- On every full Laurent edge the old action is the original variable scaling. -/
@[reassoc] theorem completeClosedLaurent_oldAction_edge (a : ZMod n) (i : Fin n) :
    (E) i ≫ (e).hom ≫ (PolygonSplitGroup.component K n a ⊗ₘ 𝟙 (C)).left ≫ (act).left =
      universalEdgeScaling K ≫
        (torusToComponent K ≫ componentι K n (rotateIndex a i) ≫ P).left := by
  rw [completeClosedLaurentProductIso_edge_assoc]
  have ht := congrArg Over.Hom.left (whiskerLeft_comp_tensorHom
    (PolygonSplitGroup.component K n a) (torusToComponent K ≫ componentι K n i ≫ P) (𝟙 C))
  simp only [Over.comp_left, Category.comp_id] at ht
  rw [reassoc_of% ht]
  have ha := congrArg Over.Hom.left (PolygonUniversalAction.torus_act K n hn P Q hp a i)
  simp only [Over.comp_left] at ha
  rw [ha, ← Category.assoc]
  have hm := universalEdgePair_mul K (completeClosedLaurentEdgePair K)
    (completeClosedLaurentEdgePair_fst K) (completeClosedLaurentEdgePair_snd K)
  rw [hm]
  rfl

/-- The entire old closed Laurent action equals scaling and the original closed rotation. -/
@[reassoc] theorem completeClosedLaurent_oldAction (a : ZMod n) :
    (e).hom ≫ (PolygonSplitGroup.component K n a ⊗ₘ 𝟙 (C)).left ≫ (act).left =
      universalScaling K 0 n h ≫ (z).inv ≫ PolygonCyclicAtlas.closedRotation K n h a := by
  let _ : IsSeparated (terminal.from (C).left) :=
    (PolygonCyclicSeparated.scheme_separated K n h).isSeparated_terminal_from
  apply edge_hom_ext K[T;T⁻¹] (LaurentPolynomial.C (0 : K)) n h
    (terminal.from (C).left)
  · exact Subsingleton.elim _ _
  · intro i
    rw [completeClosedLaurent_oldAction_edge, edge_universalScaling_assoc,
      completeClosedEdge_original_assoc, completeClosedOriginalTorus_rotation]

/-- The original and complete whole actions agree on every full closed Laurent product. -/
@[reassoc] theorem completeWholeAction_closedLaurent_comparison (i : Fin n) :
    completeClosedLaurentInput K n h i ≫ (completeWholeAction K n h).left =
      (e).hom ≫ (PolygonSplitGroup.component K n (ZMod.finEquiv n i) ⊗ₘ 𝟙 (C)).left ≫
        (act).left ≫ completeClosedFiberInclusion K n h := by
  rw [completeWholeAction_closedLaurent, completeClosedLaurent_oldAction_assoc,
    closedRotation_completeClosedFiberInclusion]

end FLT.Mazur.PolygonInfinitesimalStages
