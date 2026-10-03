/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicCocone
public import FLT.Mazur.OneGonCocone

/-!
# A specified pinching cocone for every positive polygon size

The one-gon uses its irreducible equalizer chart; larger polygons use the
cyclic node atlas. Both cases retain their specified normalization maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonAtlas

variable (K : Type u) [Field K]

/-- The polygon over K, including the irreducible one-component polygon. -/
def polygon (n : ℕ) [NeZero n] : Over (Spec (.of K)) := by
  rcases n with _ | (_ | n)
  · exact False.elim (NeZero.ne 0 rfl)
  · exact OneGonNormalization.polygon K
  · exact PolygonCyclicAtlas.polygon K (n + 2) (by omega)

/-- Normalization by the specified n projective-line components. -/
def normalization (n : ℕ) [NeZero n] : PolygonPinching.components K n ⟶ polygon K n := by
  rcases n with _ | (_ | n)
  · exact False.elim (NeZero.ne 0 rfl)
  · exact OneGonNormalization.normalizationOver K
  · exact PolygonCyclicAtlas.normalization K (n + 2) (by omega)

/-- Inclusion of the specified n pinching nodes. -/
def nodes (n : ℕ) [NeZero n] : PolygonPinching.nodes K n ⟶ polygon K n := by
  rcases n with _ | (_ | n)
  · exact False.elim (NeZero.ne 0 rfl)
  · exact OneGonNormalization.nodes K
  · exact PolygonCyclicAtlas.nodes K (n + 2) (by omega)

/-- The endpoint maps form the specified cocone in schemes over K. -/
theorem cocone (n : ℕ) [NeZero n] (hn : 0 < n) :
    PolygonPinching.toComponents K n hn ≫ normalization K n =
      PolygonPinching.toNodes K n ≫ nodes K n := by
  rcases n with _ | (_ | n)
  · omega
  · exact OneGonNormalization.cocone K hn
  · exact PolygonCyclicAtlas.cocone K (n + 2) (by omega) hn

/-- Identification with the cyclic atlas when there are at least two components. -/
def cyclicIso (n : ℕ) [NeZero n] (h : 2 ≤ n) :
    polygon K n ≅ PolygonCyclicAtlas.polygon K n h := by
  rcases n with _ | (_ | n)
  · omega
  · omega
  · exact Iso.refl _

@[reassoc (attr := simp)]
theorem normalization_cyclicIso (n : ℕ) [NeZero n] (h : 2 ≤ n) :
    normalization K n ≫ (cyclicIso K n h).hom = PolygonCyclicAtlas.normalization K n h := by
  rcases n with _ | (_ | n)
  · omega
  · omega
  · exact Category.comp_id _

@[reassoc (attr := simp)]
theorem nodes_cyclicIso (n : ℕ) [NeZero n] (h : 2 ≤ n) :
    nodes K n ≫ (cyclicIso K n h).hom = PolygonCyclicAtlas.nodes K n h := by
  rcases n with _ | (_ | n)
  · omega
  · omega
  · exact Category.comp_id _

/-- The one-component polygon is the specified one-gon cocone. -/
def oneGonIso : polygon K 1 ≅ OneGonNormalization.polygon K := Iso.refl _

@[reassoc (attr := simp)]
theorem normalization_oneGonIso : normalization K 1 ≫ (oneGonIso K).hom =
    OneGonNormalization.normalizationOver K := Category.comp_id _

@[reassoc (attr := simp)]
theorem nodes_oneGonIso : nodes K 1 ≫ (oneGonIso K).hom =
    OneGonNormalization.nodes K := Category.comp_id _

/-- The standard left component chart has the specified cyclic branch formula. -/
@[reassoc]
theorem left_component (n : ℕ) [NeZero n] (h : 2 ≤ n) (i : Fin n) :
    ProjectiveLine.left K ≫
      (PolygonPinching.componentι K n i ≫ normalization K n ≫ (cyclicIso K n h).hom).left =
      PolygonCyclicAtlas.firstBranch K ≫ PolygonCyclicAtlas.chart K n h i := by
  rw [normalization_cyclicIso, PolygonCyclicAtlas.componentι_normalization]
  exact PolygonCyclicAtlas.left_componentMap K n h i

/-- The standard right component chart maps to the cyclic predecessor. -/
@[reassoc]
theorem right_component (n : ℕ) [NeZero n] (h : 2 ≤ n) (i : Fin n) :
    ProjectiveLine.right K ≫
      (PolygonPinching.componentι K n i ≫ normalization K n ≫ (cyclicIso K n h).hom).left =
      PolygonCyclicAtlas.secondBranch K ≫
        PolygonCyclicAtlas.chart K n h ((finRotate n).symm i) := by
  rw [normalization_cyclicIso, PolygonCyclicAtlas.componentι_normalization]
  exact PolygonCyclicAtlas.right_componentMap K n h i

/-- The cyclic nodes are the actual chart origins. -/
@[reassoc]
theorem cyclic_node (n : ℕ) [NeZero n] (h : 2 ≤ n) (i : Fin n) :
    (PolygonPinching.nodeι K n i ≫ nodes K n ≫ (cyclicIso K n h).hom).left =
      PolygonNodePresentation.aOrigin K ≫ PolygonCyclicAtlas.chart K n h i := by
  rw [nodes_cyclicIso]
  exact PolygonCyclicAtlas.nodeι_nodes K n h i

end FLT.Mazur.PolygonAtlas
