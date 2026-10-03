/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodePinchingDescent

/-!
# Arbitrary-target descent on the cyclic atlas

For at least two components, endpoint-compatible projective-line maps glue
uniquely through the actual node charts and both cyclic overlaps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonCyclicDescent

open PolygonCyclicAtlas

variable (K : Type u) [Field K] (n : ℕ) (h : 2 ≤ n)
  {Y : Scheme.{u}} (f : Fin n → (ProjectiveLine.scheme K ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero K ≫ f i = ProjectiveLine.infinity K ≫ f (finRotate n i))

include w in
/-- Endpoint compatibility on the two affine branches of a node. -/
theorem condition (i : Fin n) :
    ProjectiveLine.chartZero K ≫ (ProjectiveLine.left K ≫ f i) =
      ProjectiveLine.chartZero K ≫ (ProjectiveLine.right K ≫ f (finRotate n i)) := by
  simpa only [ProjectiveLine.zero, ProjectiveLine.infinity, Category.assoc] using w i

/-- The descended map on a single node chart. -/
def localMap (i : Fin n) : PolygonNodeBranches.node K ⟶ Y :=
  (NodePinchingDescent.node_desc K (ProjectiveLine.left K ≫ f i)
    (ProjectiveLine.right K ≫ f (finRotate n i)) (condition K n f w i)).choose

@[reassoc (attr := simp)]
theorem first_localMap (i : Fin n) :
    firstBranch K ≫ localMap K n f w i = ProjectiveLine.left K ≫ f i :=
  (NodePinchingDescent.node_desc K _ _ (condition K n f w i)).choose_spec.1.1

@[reassoc (attr := simp)]
theorem second_localMap (i : Fin n) :
    secondBranch K ≫ localMap K n f w i = ProjectiveLine.right K ≫ f (finRotate n i) :=
  (NodePinchingDescent.node_desc K _ _ (condition K n f w i)).choose_spec.1.2

/-- The node descents agree on the full Laurent overlaps. -/
theorem overlap_localMap (i : Fin n) :
    PolygonNodeBranches.left K ≫ localMap K n f w i =
      (ProjectiveLine.inversion K).hom ≫ PolygonNodeBranches.right K ≫
        localMap K n f w ((finRotate n).symm i) := by
  rw [← overlap_firstBranch, Category.assoc, first_localMap,
    ← overlap_secondBranch, Category.assoc, second_localMap, Equiv.apply_symm_apply]
  rw [← Category.assoc, ← Category.assoc, ← ProjectiveLine.overlapRight,
    ProjectiveLine.overlap_condition, Category.assoc]

/-- The compatible maps on node charts and Laurent edges. -/
def descentCocone : Cocone (diagram K n) where
  pt := Y
  ι.app j := match j with
    | .left i => PolygonNodeBranches.left K ≫ localMap K n f w i
    | .right i => localMap K n f w i
  ι.naturality := by
    intro i j a
    cases a with
    | id i => simp
    | fst i => exact (Category.comp_id _).symm
    | snd i =>
      change ((ProjectiveLine.inversion K).hom ≫ PolygonNodeBranches.right K) ≫ _ = _ ≫ 𝟙 _
      simpa only [Category.assoc, Category.comp_id, shape] using
        (overlap_localMap K n f w i).symm

/-- Descent to the actual cyclic atlas. -/
def desc : scheme K n h ⟶ Y :=
  letI : Fact (2 ≤ n) := ⟨h⟩
  colimit.desc (diagram K n) (descentCocone K n f w)

@[reassoc (attr := simp)]
theorem chart_desc (i : Fin n) : chart K n h i ≫ desc K n h f w = localMap K n f w i := by
  let : Fact (2 ≤ n) := ⟨h⟩
  exact colimit.ι_desc (descentCocone K n f w) (.right i)

@[reassoc (attr := simp)]
theorem componentMap_desc (i : Fin n) : componentMap K n h i ≫ desc K n h f w = f i := by
  apply pushout.hom_ext
  · change ProjectiveLine.left K ≫ _ = ProjectiveLine.left K ≫ _
    simp only [left_componentMap_assoc, chart_desc, first_localMap]
  · change ProjectiveLine.right K ≫ _ = ProjectiveLine.right K ≫ _
    simp only [right_componentMap_assoc, chart_desc, second_localMap, Equiv.apply_symm_apply]

/-- The actual node charts as an open cover. -/
def cover : (scheme K n h).OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (Fin n)
    (fun _ ↦ PolygonNodeBranches.node K) (chart K n h)
    (fun x ↦ by obtain ⟨i, y, hy⟩ := charts_cover K n h x; exact ⟨i, y, hy⟩)
    (fun _ ↦ inferInstance)

/-- Maps from the polygon are determined by the specified projective components. -/
theorem hom_ext (d e : scheme K n h ⟶ Y)
    (he : ∀ i, componentMap K n h i ≫ d = componentMap K n h i ≫ e) : d = e := by
  apply (cover K n h).hom_ext
  intro i
  change chart K n h i ≫ d = chart K n h i ≫ e
  apply NodePinchingDescent.hom_ext K
  · simpa only [← Category.assoc, left_componentMap] using
      congrArg (fun t ↦ ProjectiveLine.left K ≫ t) (he i)
  · have hh := congrArg (fun t ↦ ProjectiveLine.right K ≫ t) (he (finRotate n i))
    simpa only [← Category.assoc, right_componentMap, Equiv.symm_apply_apply] using hh

include w in
/-- Endpoint-compatible component maps descend uniquely to every target scheme. -/
theorem existsUnique_desc : ∃! d : scheme K n h ⟶ Y, ∀ i, componentMap K n h i ≫ d = f i := by
  refine ⟨desc K n h f w, componentMap_desc K n h f w, ?_⟩
  intro e he
  exact hom_ext K n h e _ fun i ↦ (he i).trans (componentMap_desc K n h f w i).symm

end FLT.Mazur.PolygonCyclicDescent
