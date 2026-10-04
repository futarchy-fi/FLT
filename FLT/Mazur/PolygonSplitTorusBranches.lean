/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNodeAffineCharts

/-!
# The torus coordinates of the two branches of an actual split node

The first puncture is the torus on component i. The second puncture is the
inverse coordinate on component finRotate n i. The formulas keep every index,
including both indices when n = 2.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonNodeAffineCharts
open PolygonPinching
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (hn₂ : 2 ≤ n) (i : Fin n)

/-- The first normalization branch belongs to component i. -/
@[reassoc]
lemma firstBranch_splitChart :
    PolygonCyclicAtlas.firstBranch K ≫ splitChart K n hn p q h hn₂ i =
      ProjectiveLine.left K ≫ (componentι K n i ≫ p).left := by
  unfold splitChart
  rw [← Category.assoc, ← PolygonAtlas.left_component]
  change ((ProjectiveLine.left K ≫ (componentι K n i).left ≫
    (PolygonAtlas.normalization K n).left ≫ (PolygonAtlas.cyclicIso K n hn₂).hom.left) ≫
    (PolygonAtlas.cyclicIso K n hn₂).inv.left ≫ (polygonIso K n hn p q h).hom.left) = _
  simp only [Category.assoc, ← Over.comp_left, Iso.hom_inv_id_assoc,
    normalization_polygonIso]

/-- The second normalization branch belongs to the cyclic successor. -/
@[reassoc]
lemma secondBranch_splitChart :
    PolygonCyclicAtlas.secondBranch K ≫ splitChart K n hn p q h hn₂ i =
      ProjectiveLine.right K ≫ (componentι K n (finRotate n i) ≫ p).left := by
  unfold splitChart
  conv_lhs => arg 2; arg 1; rw [← Equiv.symm_apply_apply (finRotate n) i]
  rw [← Category.assoc, ← PolygonAtlas.right_component]
  change ((ProjectiveLine.right K ≫ (componentι K n (finRotate n i)).left ≫
    (PolygonAtlas.normalization K n).left ≫ (PolygonAtlas.cyclicIso K n hn₂).hom.left) ≫
    (PolygonAtlas.cyclicIso K n hn₂).inv.left ≫ (polygonIso K n hn p q h).hom.left) = _
  simp only [Category.assoc, ← Over.comp_left, Iso.hom_inv_id_assoc,
    normalization_polygonIso]

/-- The first punctured branch is the actual torus map with its original coordinate. -/
@[reassoc]
lemma left_splitChart :
    PolygonNodeBranches.left K ≫ splitChart K n hn p q h hn₂ i =
      (torusToComponent K ≫ componentι K n i ≫ p).left := by
  rw [← PolygonCyclicAtlas.overlap_firstBranch, Category.assoc, firstBranch_splitChart]
  rfl

/-- The second punctured branch uses the inverse of the next component coordinate. -/
@[reassoc]
lemma right_splitChart :
    PolygonNodeBranches.right K ≫ splitChart K n hn p q h hn₂ i =
      (ProjectiveLine.inversion K).inv ≫
        (torusToComponent K ≫ componentι K n (finRotate n i) ≫ p).left := by
  rw [← PolygonCyclicAtlas.overlap_secondBranch, Category.assoc, secondBranch_splitChart]
  change ProjectiveLine.overlapLeft K ≫ ProjectiveLine.right K ≫ _ =
    (ProjectiveLine.inversion K).inv ≫ (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) ≫ _
  rw [ProjectiveLine.overlap_condition, ProjectiveLine.overlapRight]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end FLT.Mazur.PolygonNodeAffineCharts
