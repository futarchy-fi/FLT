/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOneGonContraction
public import FLT.Mazur.PolygonPinchingFlatBaseChange

/-!
# Contraction commutes with base change of the actual pinching diagram

Over any scheme over the original field, descend the original pulled-back
normalization and node maps. The result equals pullback of the original
proper surjective contraction, by the preserved pinching pushout.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonOneGonContraction
open PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q) (i : Fin n)
  {T : Scheme} (g : T ⟶ Spec (.of K))

/-- Descend the actual normalization and node contraction maps after base change. -/
def baseChangedContraction :
    (Over.pullback g).obj C ⟶ (Over.pullback g).obj (PolygonAtlas.polygon K 1) :=
  (PolygonPinchingFlatBaseChange.pinching_pullback K n g hn p q h).desc
    ((Over.pullback g).map (normalizationMap K n i))
    ((Over.pullback g).map (nodesMap K n)) (by
      rw [← Functor.map_comp, ← Functor.map_comp, cocone K n i hn])

/-- Base change and descent give exactly the same contraction of the original schemes. -/
theorem baseChangedContraction_eq :
    baseChangedContraction K n hn p q h i g =
      (Over.pullback g).map (contraction K n hn p q h i) := by
  apply (PolygonPinchingFlatBaseChange.pinching_pullback K n g hn p q h).hom_ext
  · rw [← Functor.map_comp, normalization_contraction]
    exact (PolygonPinchingFlatBaseChange.pinching_pullback K n g hn p q h).inl_desc _ _ _
  · rw [← Functor.map_comp, nodes_contraction]
    exact (PolygonPinchingFlatBaseChange.pinching_pullback K n g hn p q h).inr_desc _ _ _

/-- The retained complete component keeps its exact pulled-back normalization map. -/
@[reassoc] theorem retained_baseChangedContraction :
    (Over.pullback g).map (componentι K n i ≫ p) ≫
        baseChangedContraction K n hn p q h i g =
      (Over.pullback g).map (retainedComponent K) := by
  rw [baseChangedContraction_eq, ← Functor.map_comp, Category.assoc, retained_contraction]

/-- Every omitted complete component remains collapsed to the original pulled-back node. -/
@[reassoc] theorem omitted_baseChangedContraction {j : Fin n} (hj : j ≠ i) :
    (Over.pullback g).map (componentι K n j ≫ p) ≫
        baseChangedContraction K n hn p q h i g =
      (Over.pullback g).map (componentToPoint K ≫ targetNode K) := by
  rw [baseChangedContraction_eq, ← Functor.map_comp, Category.assoc,
    omitted_contraction K n hn p q h i hj]

/-- The descended contraction remains proper on the entire base-changed curve. -/
theorem baseChangedContraction_proper :
    IsProper (baseChangedContraction K n hn p q h i g).left := by
  rw [baseChangedContraction_eq]
  exact MorphismProperty.of_isPullback
    (OverPullbackLocalPushout.map_isPullback g (contraction K n hn p q h i)).flip
    (contraction_proper K n hn p q h i)

/-- The descended contraction remains surjective, even on nonreduced parameter schemes. -/
theorem baseChangedContraction_surjective :
    Surjective (baseChangedContraction K n hn p q h i g).left := by
  rw [baseChangedContraction_eq]
  exact MorphismProperty.of_isPullback
    (OverPullbackLocalPushout.map_isPullback g (contraction K n hn p q h i)).flip
    (contraction_surjective K n hn p q h i)

end FLT.Mazur.PolygonOneGonContraction
