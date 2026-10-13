/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOneGonContractionDiagram
public import FLT.Mazur.PolygonComponentImages

/-!
# The actual component contraction to the original one-gon

Descend the explicit normalization/node diagram through the original polygon
pushout. The resulting map is proper and surjective, retains the selected
projective component, and collapses every other component to the actual node.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonOneGonContraction
open PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q) (i : Fin n)

/-- The original polygon map retaining one component and contracting all the others. -/
def contraction : C ⟶ PolygonAtlas.polygon K 1 :=
  h.desc (normalizationMap K n i) (nodesMap K n) (cocone K n i hn)

/-- The descended map agrees with every actual normalization component. -/
@[reassoc] theorem normalization_contraction :
    p ≫ contraction K n hn p q h i = normalizationMap K n i := by
  simp [contraction]

/-- The descended map retains every original node map. -/
@[reassoc] theorem nodes_contraction :
    q ≫ contraction K n hn p q h i = nodesMap K n := by
  simp [contraction]

/-- The retained original component becomes the complete target normalization. -/
@[reassoc] theorem retained_contraction :
    componentι K n i ≫ p ≫ contraction K n hn p q h i = retainedComponent K := by
  rw [normalization_contraction, component_normalizationMap, ite_eq_left rfl]

/-- Every omitted complete component is contracted to the original target node. -/
@[reassoc] theorem omitted_contraction {j : Fin n} (hj : j ≠ i) :
    componentι K n j ≫ p ≫ contraction K n hn p q h i =
      componentToPoint K ≫ targetNode K := by
  rw [normalization_contraction, component_normalizationMap, ite_eq_right hj]

/-- Every original node is mapped to the same actual one-gon node. -/
@[reassoc] theorem node_contraction (j : Fin n) :
    nodeι K n j ≫ q ≫ contraction K n hn p q h i = targetNode K := by
  rw [nodes_contraction, node_nodesMap]

/-- The normalization and node formulas determine the entire contraction uniquely. -/
theorem contraction_unique (f : C ⟶ PolygonAtlas.polygon K 1)
    (hp : p ≫ f = normalizationMap K n i) (hq : q ≫ f = nodesMap K n) :
    f = contraction K n hn p q h i := by
  apply h.hom_ext
  · rw [hp, normalization_contraction]
  · rw [hq, nodes_contraction]

/-- The map is proper on the entire original reducible polygon. -/
theorem contraction_proper : IsProper (contraction K n hn p q h i).left := by
  let _ : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let _ := PolygonSeparated.cocone K 1 (by decide)
    (PolygonAtlas.normalization K 1) (PolygonAtlas.nodes K 1)
    (PolygonAtlas.isPushout K 1 (by decide))
  let _ := PolygonProper.proper K n hn p q h
  have : IsProper ((contraction K n hn p q h i).left ≫ (PolygonAtlas.polygon K 1).hom) := by
    rw [Over.w]
    infer_instance
  exact IsProper.of_comp _ (PolygonAtlas.polygon K 1).hom

/-- The retained component covers the target, so the original contraction is surjective. -/
theorem contraction_surjective : Surjective (contraction K n hn p q h i).left := by
  constructor
  intro x
  obtain ⟨j, y, hy⟩ := PolygonComponentImages.cover K 1 (by decide)
    (PolygonAtlas.normalization K 1) (PolygonAtlas.nodes K 1)
    (PolygonAtlas.isPushout K 1 (by decide)) x
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  refine ⟨(componentι K n i ≫ p).left y, ?_⟩
  have he := congrArg (fun f ↦ f.left y) (retained_contraction K n hn p q h i)
  exact he.trans hy

end FLT.Mazur.PolygonOneGonContraction
