/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCollapsedChainCartesianAtlas

/-!
# Laurent opens in the actual chain-chart intersections

Each omitted cyclic edge gives an open immersion into the Cartesian overlap
of its two incident charts. Both orientations remain available for the two-gon.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonCollapsedChainOverlapEdges
open PolygonCollapsedChainOpenCover PolygonCollapsedChainCartesianAtlas
open PolygonCollapsedChainLaurentEdges
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) (i : Fin n)

instance firstEdge_isOpenImmersion (a : ChartIndex n i) (ha : nodeIndex n i a ≠ i) :
    IsOpenImmersion (firstEdge K n h i a ha) := by
  have : IsOpenImmersion (firstEdge K n h i a ha ≫ chartMap K n h i a) := by
    rw [firstEdge_chartMap]
    infer_instance
  exact IsOpenImmersion.of_comp _ (chartMap K n h i a)

instance secondEdge_isOpenImmersion (a : ChartIndex n i) (j : Fin n) (hj : j ≠ i)
    (ha : (finRotate n).symm j = nodeIndex n i a) :
    IsOpenImmersion (secondEdge K n h i a j hj ha) := by
  have : IsOpenImmersion (secondEdge K n h i a j hj ha ≫ chartMap K n h i a) := by
    rw [secondEdge_chartMap]
    infer_instance
  exact IsOpenImmersion.of_comp _ (chartMap K n h i a)

/-- The forward cyclic edge as a map to the full Cartesian chart intersection. -/
def forward (a b : ChartIndex n i) (ha : nodeIndex n i a ≠ i)
    (hab : (finRotate n).symm (nodeIndex n i a) = nodeIndex n i b) :
    ProjectiveLine.overlap K ⟶ pullback (chartMap K n h i a) (chartMap K n h i b) :=
  pullback.lift (firstEdge K n h i a ha)
    (secondEdge K n h i b (nodeIndex n i a) ha hab)
    (by rw [firstEdge_chartMap, secondEdge_chartMap])

@[reassoc] theorem forward_fst (a b : ChartIndex n i) (ha : nodeIndex n i a ≠ i)
    (hab : (finRotate n).symm (nodeIndex n i a) = nodeIndex n i b) :
    forward K n h i a b ha hab ≫ pullback.fst _ _ = firstEdge K n h i a ha :=
  pullback.lift_fst _ _ _

@[reassoc] theorem forward_snd (a b : ChartIndex n i) (ha : nodeIndex n i a ≠ i)
    (hab : (finRotate n).symm (nodeIndex n i a) = nodeIndex n i b) :
    forward K n h i a b ha hab ≫ pullback.snd _ _ =
      secondEdge K n h i b (nodeIndex n i a) ha hab :=
  pullback.lift_snd _ _ _

instance forward_isOpenImmersion (a b : ChartIndex n i) (ha : nodeIndex n i a ≠ i)
    (hab : (finRotate n).symm (nodeIndex n i a) = nodeIndex n i b) :
    IsOpenImmersion (forward K n h i a b ha hab) := by
  have : IsOpenImmersion (forward K n h i a b ha hab ≫ pullback.fst _ _) := by
    rw [forward_fst]
    infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.fst _ _)

/-- The reverse cyclic edge, still present separately when there are two nodes. -/
def reverse (a b : ChartIndex n i) (hb : nodeIndex n i b ≠ i)
    (hba : (finRotate n).symm (nodeIndex n i b) = nodeIndex n i a) :
    ProjectiveLine.overlap K ⟶ pullback (chartMap K n h i a) (chartMap K n h i b) :=
  pullback.lift (secondEdge K n h i a (nodeIndex n i b) hb hba)
    (firstEdge K n h i b hb)
    (by rw [secondEdge_chartMap, firstEdge_chartMap])

@[reassoc] theorem reverse_fst (a b : ChartIndex n i) (hb : nodeIndex n i b ≠ i)
    (hba : (finRotate n).symm (nodeIndex n i b) = nodeIndex n i a) :
    reverse K n h i a b hb hba ≫ pullback.fst _ _ =
      secondEdge K n h i a (nodeIndex n i b) hb hba :=
  pullback.lift_fst _ _ _

@[reassoc] theorem reverse_snd (a b : ChartIndex n i) (hb : nodeIndex n i b ≠ i)
    (hba : (finRotate n).symm (nodeIndex n i b) = nodeIndex n i a) :
    reverse K n h i a b hb hba ≫ pullback.snd _ _ = firstEdge K n h i b hb :=
  pullback.lift_snd _ _ _

instance reverse_isOpenImmersion (a b : ChartIndex n i) (hb : nodeIndex n i b ≠ i)
    (hba : (finRotate n).symm (nodeIndex n i b) = nodeIndex n i a) :
    IsOpenImmersion (reverse K n h i a b hb hba) := by
  have : IsOpenImmersion (reverse K n h i a b hb hba ≫ pullback.snd _ _) := by
    rw [reverse_snd]
    infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.snd _ _)

end FLT.Mazur.PolygonCollapsedChainOverlapEdges
