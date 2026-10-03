/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicAtlas
public import FLT.Mazur.PolygonNodePresentation
public import FLT.Mazur.PolygonPinchingDiagram

/-!
# The normalization cocone of the cyclic atlas

The two affine charts of each specified projective line map to adjacent node
charts. Their Laurent restrictions agree, so they glue to an actual morphism.
Zero and infinity give exactly the cyclic pinching cocone. This does not assert
its universal property for arbitrary target schemes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonCyclicAtlas

variable (K : Type u) [Field K]

/-- The first affine branch of the normalization of a node. -/
def firstBranch : ProjectiveLine.chart K ⟶ PolygonNodeBranches.node K :=
  Spec.map (CommRingCat.ofHom (PolygonNodeEqualizer.first (R := K)).toRingHom)

/-- The second affine branch of the normalization of a node. -/
def secondBranch : ProjectiveLine.chart K ⟶ PolygonNodeBranches.node K :=
  Spec.map (CommRingCat.ofHom (PolygonNodeEqualizer.second (R := K)).toRingHom)

@[reassoc (attr := simp)]
theorem overlap_firstBranch :
    ProjectiveLine.overlapLeft K ≫ firstBranch K = PolygonNodeBranches.left K := by
  rw [ProjectiveLine.overlapLeft, firstBranch, ← Spec.map_comp]
  rfl

@[reassoc (attr := simp)]
theorem overlap_secondBranch :
    ProjectiveLine.overlapLeft K ≫ secondBranch K = PolygonNodeBranches.right K := by
  rw [ProjectiveLine.overlapLeft, secondBranch, ← Spec.map_comp]
  rfl

@[reassoc (attr := simp)]
theorem firstBranch_toBase :
    firstBranch K ≫ PolygonNodeBranches.toBase K = ProjectiveLine.chartToBase K := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

@[reassoc (attr := simp)]
theorem secondBranch_toBase :
    secondBranch K ≫ PolygonNodeBranches.toBase K = ProjectiveLine.chartToBase K := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

@[reassoc (attr := simp)]
theorem zero_firstBranch :
    ProjectiveLine.chartZero K ≫ firstBranch K = PolygonNodePresentation.aOrigin K := by
  rw [ProjectiveLine.chartZero, firstBranch, ← Spec.map_comp]
  rfl

@[reassoc (attr := simp)]
theorem zero_secondBranch :
    ProjectiveLine.chartZero K ≫ secondBranch K = PolygonNodePresentation.aOrigin K := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext p
  exact p.property.symm

@[reassoc (attr := simp)]
theorem origin_toBase :
    PolygonNodePresentation.aOrigin K ≫ PolygonNodeBranches.toBase K = 𝟙 _ := by
  rw [← zero_firstBranch, Category.assoc, firstBranch_toBase, ProjectiveLine.chartZero_toBase]

variable (n : ℕ) (h : 2 ≤ n)

/-- The cyclic atlas regarded as a scheme over the base field. -/
def polygon : Over (Spec (.of K)) := Over.mk (toBase K n h)

/-- The two affine pieces of a normalization component agree on their punctures. -/
theorem component_overlap (i : Fin n) :
    ProjectiveLine.overlapLeft K ≫ firstBranch K ≫ chart K n h i =
      ProjectiveLine.overlapRight K ≫ secondBranch K ≫
        chart K n h ((finRotate n).symm i) := by
  rw [overlap_firstBranch_assoc, ProjectiveLine.overlapRight, Category.assoc,
    overlap_secondBranch_assoc]
  exact overlap K n h i

/-- The specified projective line maps to its two adjacent node charts. -/
def componentMap (i : Fin n) : ProjectiveLine.scheme K ⟶ scheme K n h :=
  pushout.desc (firstBranch K ≫ chart K n h i)
    (secondBranch K ≫ chart K n h ((finRotate n).symm i)) (component_overlap K n h i)

@[reassoc (attr := simp)]
theorem left_componentMap (i : Fin n) :
    ProjectiveLine.left K ≫ componentMap K n h i = firstBranch K ≫ chart K n h i :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem right_componentMap (i : Fin n) :
    ProjectiveLine.right K ≫ componentMap K n h i =
      secondBranch K ≫ chart K n h ((finRotate n).symm i) :=
  pushout.inr_desc _ _ _

@[reassoc (attr := simp)]
theorem componentMap_toBase (i : Fin n) :
    componentMap K n h i ≫ toBase K n h = ProjectiveLine.toBase K := by
  apply pushout.hom_ext
  · change ProjectiveLine.left K ≫ componentMap K n h i ≫ toBase K n h =
      ProjectiveLine.left K ≫ ProjectiveLine.toBase K
    rw [left_componentMap_assoc, chart_toBase, firstBranch_toBase,
      ProjectiveLine.left_toBase]
  · change ProjectiveLine.right K ≫ componentMap K n h i ≫ toBase K n h =
      ProjectiveLine.right K ≫ ProjectiveLine.toBase K
    rw [right_componentMap_assoc, chart_toBase, secondBranch_toBase,
      ProjectiveLine.right_toBase]

@[reassoc (attr := simp)]
theorem zero_componentMap (i : Fin n) :
    ProjectiveLine.zero K ≫ componentMap K n h i =
      PolygonNodePresentation.aOrigin K ≫ chart K n h i := by
  simp [ProjectiveLine.zero]

@[reassoc (attr := simp)]
theorem infinity_componentMap (i : Fin n) :
    ProjectiveLine.infinity K ≫ componentMap K n h i =
      PolygonNodePresentation.aOrigin K ≫ chart K n h ((finRotate n).symm i) := by
  simp [ProjectiveLine.infinity]

/-- The successor in the pinching span is the cyclic permutation used by the atlas. -/
theorem next_eq_rotate (hn : 0 < n) (i : Fin n) :
    PolygonPinching.next hn i = finRotate n i := by
  let : NeZero n := ⟨by omega⟩
  rw [finRotate_apply]
  apply Fin.ext
  simp [PolygonPinching.next, Fin.val_add, Nat.add_mod]

/-- The normalization map from the coproduct of the specified projective lines. -/
def normalization : PolygonPinching.components K n ⟶ polygon K n h :=
  Sigma.desc fun i ↦ Over.homMk (componentMap K n h i) (componentMap_toBase K n h i)

/-- The map from the coproduct of nodes. -/
def nodes : PolygonPinching.nodes K n ⟶ polygon K n h :=
  Sigma.desc fun i ↦ Over.homMk (PolygonNodePresentation.aOrigin K ≫ chart K n h i)
    (by
      change (PolygonNodePresentation.aOrigin K ≫ chart K n h i) ≫ toBase K n h = 𝟙 _
      simp)

@[reassoc (attr := simp)]
theorem componentι_normalization (i : Fin n) :
    PolygonPinching.componentι K n i ≫ normalization K n h =
      Over.homMk (componentMap K n h i) (componentMap_toBase K n h i) := by
  simp [PolygonPinching.componentι, normalization]

@[reassoc]
theorem nodeι_nodes (i : Fin n) :
    (PolygonPinching.nodeι K n i ≫ nodes K n h).left =
      PolygonNodePresentation.aOrigin K ≫ chart K n h i := by
  simp only [PolygonPinching.nodeι, nodes, Sigma.ι_comp_desc]
  rfl

/-- Each zero endpoint maps to the corresponding node. -/
@[reassoc]
theorem zeroSection_normalization (i : Fin n) :
    PolygonPinching.endpoint K n (by omega) i false ≫ normalization K n h =
      PolygonPinching.nodeι K n i ≫ nodes K n h := by
  change ProjectiveLine.zeroSection K ≫ PolygonPinching.componentι K n i ≫
    normalization K n h = _
  rw [componentι_normalization]
  apply Over.OverMorphism.ext
  change ProjectiveLine.zero K ≫ componentMap K n h i =
    (PolygonPinching.nodeι K n i ≫ nodes K n h).left
  rw [zero_componentMap, nodeι_nodes]

/-- Each infinity endpoint maps to the preceding node, as specified in the span. -/
@[reassoc]
theorem infinitySection_normalization (hn : 0 < n) (i : Fin n) :
    PolygonPinching.endpoint K n hn i true ≫ normalization K n h =
      PolygonPinching.nodeι K n i ≫ nodes K n h := by
  change ProjectiveLine.infinitySection K ≫
    PolygonPinching.componentι K n (PolygonPinching.next hn i) ≫ normalization K n h = _
  rw [componentι_normalization]
  apply Over.OverMorphism.ext
  change ProjectiveLine.infinity K ≫ componentMap K n h (PolygonPinching.next hn i) =
    (PolygonPinching.nodeι K n i ≫ nodes K n h).left
  rw [infinity_componentMap, nodeι_nodes, next_eq_rotate, Equiv.symm_apply_apply]

/-- The constructed morphisms form the specified cyclic pinching cocone. -/
theorem cocone (hn : 0 < n) :
    PolygonPinching.toComponents K n hn ≫ normalization K n h =
      PolygonPinching.toNodes K n ≫ nodes K n h := by
  apply Sigma.hom_ext
  intro ib
  rcases ib with ⟨i, b⟩
  cases b
  · simpa [PolygonPinching.toComponents, PolygonPinching.toNodes] using
      zeroSection_normalization K n h i
  · simpa [PolygonPinching.toComponents, PolygonPinching.toNodes] using
      infinitySection_normalization K n h hn i

end FLT.Mazur.PolygonCyclicAtlas
