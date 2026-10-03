/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SeparatedOpenCover
public import FLT.Mazur.PolygonCyclicNormalizationFinite
public import FLT.Mazur.CyclicOverlapGraph
/-!
# Separatedness of the cyclic polygon

Distinct chart intersections are the union of their available closed edge
graphs. Both edges are retained when n=2. Equal chart pairs use the affine
diagonal, and the product cover assembles these tests.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.PolygonCyclicSeparated
variable (K : Type u) [Field K] (n : ℕ) (h : 2 ≤ n)
open PolygonCyclicAtlas
/-- The common product of two node charts over K. -/
abbrev product := pullback (PolygonNodeBranches.toBase K) (PolygonNodeBranches.toBase K)
/-- Identify each chart product using its specified structure morphism. -/
def productIso (i j : Fin n) :
    pullback (chart K n h i ≫ toBase K n h) (chart K n h j ≫ toBase K n h) ≅ product K :=
  pullback.congrHom (chart_toBase K n h i) (chart_toBase K n h j)
/-- The actual intersection map in the common chart product. -/
def overlapMap (i j : Fin n) : pullback (chart K n h i) (chart K n h j) ⟶ product K :=
  pullback.mapDesc (chart K n h i) (chart K n h j) (toBase K n h) ≫
    (productIso K n h i j).hom
@[reassoc (attr := simp)] theorem overlapMap_fst (i j : Fin n) :
    overlapMap K n h i j ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [overlapMap, productIso, pullback.mapDesc]
@[reassoc (attr := simp)] theorem overlapMap_snd (i j : Fin n) :
    overlapMap K n h i j ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [overlapMap, productIso, pullback.mapDesc]
/-- The Laurent edge as a map to the actual chart intersection. -/
def edge (i j : Fin n) (e : (finRotate n).symm i = j) :
    ProjectiveLine.overlap K ⟶ pullback (chart K n h i) (chart K n h j) :=
  pullback.lift (PolygonNodeBranches.left K)
    ((ProjectiveLine.inversion K).hom ≫ PolygonNodeBranches.right K)
    (by subst j; exact overlap K n h i)
@[reassoc] theorem edge_overlapMap (i j : Fin n) (e : (finRotate n).symm i = j) :
    edge K n h i j e ≫ overlapMap K n h i j = CyclicOverlapGraph.graph K := by
  apply pullback.hom_ext <;> simp [edge, CyclicOverlapGraph.graph]
/-- The same edge with its chart factors exchanged. -/
def reverseGraph : ProjectiveLine.overlap K ⟶ product K :=
  CyclicOverlapGraph.graph K ≫ (pullbackSymmetry _ _).hom
instance reverseGraph_closed : IsClosedImmersion (reverseGraph K) := by
  unfold reverseGraph
  infer_instance
@[reassoc] theorem symmetry_overlapMap (i j : Fin n) :
    (pullbackSymmetry (chart K n h i) (chart K n h j)).hom ≫
      overlapMap K n h j i = overlapMap K n h i j ≫ (pullbackSymmetry _ _).hom := by
  apply pullback.hom_ext <;> simp
/-- An intersection contains exactly its available cyclic edge graphs. -/
theorem range_overlapMap (i j : Fin n) (hne : i ≠ j) :
    Set.range (overlapMap K n h i j) =
      {z | (finRotate n).symm i = j ∧ z ∈ Set.range (CyclicOverlapGraph.graph K)} ∪
      {z | (finRotate n).symm j = i ∧ z ∈ Set.range (reverseGraph K)} := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    have hp : chart K n h i (pullback.fst (chart K n h i) (chart K n h j) p) =
        chart K n h j (pullback.snd (chart K n h i) (chart K n h j) p) :=
      congrArg (fun f ↦ f p) (pullback.condition (f := chart K n h i) (g := chart K n h j))
    rcases (charts_eq_iff K n h hne _ _).mp hp with
      ⟨t, e, ht, _⟩ | ⟨t, e, _, ht⟩
    · left
      refine ⟨e, t, ?_⟩
      have he : edge K n h i j e t = p := by
        apply (pullback.fst (chart K n h i) (chart K n h j)).isOpenEmbedding.injective
        change (edge K n h i j e ≫ pullback.fst _ _) t = _
        simpa [edge] using ht
      rw [← he]
      exact congrArg (fun f ↦ f t) (edge_overlapMap K n h i j e).symm
    · right
      refine ⟨e, t, ?_⟩
      have he : ((edge K n h j i e) ≫
          (pullbackSymmetry (chart K n h j) (chart K n h i)).hom) t = p := by
        apply (pullback.snd (chart K n h i) (chart K n h j)).isOpenEmbedding.injective
        change ((edge K n h j i e ≫ (pullbackSymmetry _ _).hom) ≫ pullback.snd _ _) t = _
        simpa [edge] using ht
      rw [← he]
      have eqn : edge K n h j i e ≫ (pullbackSymmetry _ _).hom ≫ overlapMap K n h i j =
          reverseGraph K := by
        rw [symmetry_overlapMap, ← Category.assoc, edge_overlapMap]
        rfl
      exact congrArg (fun f ↦ f t) eqn.symm
  · rintro (⟨e, t, rfl⟩ | ⟨e, t, rfl⟩)
    · exact ⟨edge K n h i j e t, congrArg (fun f ↦ f t) (edge_overlapMap K n h i j e)⟩
    · refine ⟨((edge K n h j i e) ≫ (pullbackSymmetry _ _).hom) t, ?_⟩
      change ((edge K n h j i e ≫ (pullbackSymmetry _ _).hom) ≫ overlapMap K n h i j) t = _
      rw [Category.assoc, symmetry_overlapMap, ← Category.assoc, edge_overlapMap]
      rfl
/-- Every chart intersection is closed in the product of its charts. -/
theorem overlap_closed (i j : Fin n) : IsClosedImmersion (overlapMap K n h i j) := by
  by_cases he : i = j
  · subst j
    have eqn : overlapMap K n h i i = pullback.fst _ _ ≫
        pullback.diagonal (PolygonNodeBranches.toBase K) := by
      apply pullback.hom_ext
      · simp
      · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, overlapMap_snd]
        exact (cancel_mono (chart K n h i)).mp pullback.condition.symm
    rw [eqn]
    infer_instance
  · have : IsPreimmersion (overlapMap K n h i j) := by
      unfold overlapMap
      infer_instance
    apply IsClosedImmersion.of_isPreimmersion
    rw [range_overlapMap K n h i j he]
    apply IsClosed.union
    · by_cases e : (finRotate n).symm i = j
      · simpa only [e, true_and, Set.ofPred_mem_eq] using
          (CyclicOverlapGraph.graph K).isClosedEmbedding.isClosed_range
      · simp only [e, false_and, Set.ofPred_false]; exact isClosed_empty
    · by_cases e : (finRotate n).symm j = i
      · simpa only [e, true_and, Set.ofPred_mem_eq] using
          (reverseGraph K).isClosedEmbedding.isClosed_range
      · simp only [e, false_and, Set.ofPred_false]; exact isClosed_empty
/-- The cyclic polygon is separated over K, including n=2. -/
theorem separated : IsSeparated (toBase K n h) := by
  apply SeparatedOpenCover.of_pairwise _ (PolygonCyclicNormalizationFinite.targetCover K n h)
  intro i j
  exact (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
    (productIso K n h i j).hom).mp (overlap_closed K n h i j)
instance scheme_separated : (scheme K n h).IsSeparated := by
  have := separated K n h
  constructor
  rw [← terminal.comp_from (toBase K n h)]
  infer_instance
end FLT.Mazur.PolygonCyclicSeparated
