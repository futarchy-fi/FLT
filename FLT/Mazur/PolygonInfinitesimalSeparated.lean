/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SeparatedOpenCover
public import FLT.Mazur.PolygonInfinitesimalFamily
public import FLT.Mazur.PolygonSmoothingOverlapGraph
/-!
# Separatedness of the arithmetic infinitesimal polygon

Distinct chart intersections are the union of their available closed edge
graphs. Both edges are retained when n=2. Equal chart pairs use the affine
diagonal, and the product cover assembles these tests.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.PolygonInfinitesimalSeparated
variable (R : Type u) [CommRing R] (q : R) [Fact (IsNilpotent q)]
  (n : ℕ) (h : 2 ≤ n)
open PolygonInfinitesimal
open PolygonSmoothing (branchTorus)
/-- The common product of two node charts over R. -/
abbrev product :=
  pullback (PolygonSmoothing.chartStructure R q) (PolygonSmoothing.chartStructure R q)
/-- Identify each chart product using its specified structure morphism. -/
def productIso (i j : Fin n) :
    pullback (chart R q n h i ≫ toBase R q n h) (chart R q n h j ≫ toBase R q n h) ≅ product R q :=
  pullback.congrHom (chart_toBase R q n h i) (chart_toBase R q n h j)
/-- The actual intersection map in the common chart product. -/
def overlapMap (i j : Fin n) : pullback (chart R q n h i) (chart R q n h j) ⟶ product R q :=
  pullback.mapDesc (chart R q n h i) (chart R q n h j) (toBase R q n h) ≫
    (productIso R q n h i j).hom
@[reassoc (attr := simp)] theorem overlapMap_fst (i j : Fin n) :
    overlapMap R q n h i j ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [overlapMap, productIso, pullback.mapDesc]
@[reassoc (attr := simp)] theorem overlapMap_snd (i j : Fin n) :
    overlapMap R q n h i j ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [overlapMap, productIso, pullback.mapDesc]
/-- The Laurent edge as a map to the actual chart intersection. -/
def edge (i j : Fin n) (e : (finRotate n).symm i = j) :
    branchTorus R ⟶ pullback (chart R q n h i) (chart R q n h j) :=
  pullback.lift (PolygonSmoothing.leftBranchOpen R q)
    (PolygonSmoothing.precedingBranch R q)
    (by subst j; exact overlap R q n h i)
@[reassoc] theorem edge_overlapMap (i j : Fin n) (e : (finRotate n).symm i = j) :
    edge R q n h i j e ≫ overlapMap R q n h i j = PolygonSmoothing.edgeGraph R q := by
  apply pullback.hom_ext <;> simp [edge, PolygonSmoothing.edgeGraph]
/-- The same edge with its chart factors exchanged. -/
def reverseGraph : branchTorus R ⟶ product R q :=
  PolygonSmoothing.edgeGraph R q ≫ (pullbackSymmetry _ _).hom
instance reverseGraph_closed : IsClosedImmersion (reverseGraph R q) := by
  unfold reverseGraph
  infer_instance
@[reassoc] theorem symmetry_overlapMap (i j : Fin n) :
    (pullbackSymmetry (chart R q n h i) (chart R q n h j)).hom ≫
      overlapMap R q n h j i = overlapMap R q n h i j ≫ (pullbackSymmetry _ _).hom := by
  apply pullback.hom_ext <;> simp
/-- An intersection contains exactly its available cyclic edge graphs. -/
theorem range_overlapMap (i j : Fin n) (hne : i ≠ j) :
    Set.range (overlapMap R q n h i j) =
      {z | (finRotate n).symm i = j ∧ z ∈ Set.range (PolygonSmoothing.edgeGraph R q)} ∪
      {z | (finRotate n).symm j = i ∧ z ∈ Set.range (reverseGraph R q)} := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    have hp : chart R q n h i (pullback.fst (chart R q n h i) (chart R q n h j) p) =
        chart R q n h j (pullback.snd (chart R q n h i) (chart R q n h j) p) :=
      congrArg (fun f ↦ f p) (pullback.condition (f := chart R q n h i) (g := chart R q n h j))
    rcases (charts_eq_iff R q n h hne _ _).mp hp with
      ⟨t, e, ht, _⟩ | ⟨t, e, _, ht⟩
    · left
      refine ⟨e, t, ?_⟩
      have he : edge R q n h i j e t = p := by
        apply (pullback.fst (chart R q n h i) (chart R q n h j)).isOpenEmbedding.injective
        change (edge R q n h i j e ≫ pullback.fst _ _) t = _
        simpa [edge] using ht
      rw [← he]
      exact congrArg (fun f ↦ f t) (edge_overlapMap R q n h i j e).symm
    · right
      refine ⟨e, t, ?_⟩
      have he : ((edge R q n h j i e) ≫
          (pullbackSymmetry (chart R q n h j) (chart R q n h i)).hom) t = p := by
        apply (pullback.snd (chart R q n h i) (chart R q n h j)).isOpenEmbedding.injective
        change ((edge R q n h j i e ≫ (pullbackSymmetry _ _).hom) ≫ pullback.snd _ _) t = _
        simpa [edge] using ht
      rw [← he]
      have eqn : edge R q n h j i e ≫ (pullbackSymmetry _ _).hom ≫ overlapMap R q n h i j =
          reverseGraph R q := by
        rw [symmetry_overlapMap, ← Category.assoc, edge_overlapMap]
        rfl
      exact congrArg (fun f ↦ f t) eqn.symm
  · rintro (⟨e, t, rfl⟩ | ⟨e, t, rfl⟩)
    · exact ⟨edge R q n h i j e t, congrArg (fun f ↦ f t) (edge_overlapMap R q n h i j e)⟩
    · refine ⟨((edge R q n h j i e) ≫ (pullbackSymmetry _ _).hom) t, ?_⟩
      change ((edge R q n h j i e ≫ (pullbackSymmetry _ _).hom) ≫ overlapMap R q n h i j) t = _
      rw [Category.assoc, symmetry_overlapMap, ← Category.assoc, edge_overlapMap]
      rfl
/-- Every chart intersection is closed in the product of its charts. -/
theorem overlap_closed (i j : Fin n) : IsClosedImmersion (overlapMap R q n h i j) := by
  by_cases he : i = j
  · subst j
    have eqn : overlapMap R q n h i i = pullback.fst _ _ ≫
        pullback.diagonal (PolygonSmoothing.chartStructure R q) := by
      apply pullback.hom_ext
      · simp
      · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, overlapMap_snd]
        exact (cancel_mono (chart R q n h i)).mp pullback.condition.symm
    rw [eqn]
    infer_instance
  · have : IsPreimmersion (overlapMap R q n h i j) := by
      unfold overlapMap
      infer_instance
    apply IsClosedImmersion.of_isPreimmersion
    rw [range_overlapMap R q n h i j he]
    apply IsClosed.union
    · by_cases e : (finRotate n).symm i = j
      · simpa only [e, true_and, Set.ofPred_mem_eq] using
          (PolygonSmoothing.edgeGraph R q).isClosedEmbedding.isClosed_range
      · simp only [e, false_and, Set.ofPred_false]; exact isClosed_empty
    · by_cases e : (finRotate n).symm j = i
      · simpa only [e, true_and, Set.ofPred_mem_eq] using
          (reverseGraph R q).isClosedEmbedding.isClosed_range
      · simp only [e, false_and, Set.ofPred_false]; exact isClosed_empty
/-- The cyclic polygon is separated over R q, including n=2. -/
theorem separated : IsSeparated (toBase R q n h) := by
  apply SeparatedOpenCover.of_pairwise _ (chartCover R q n h)
  intro i j
  exact (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
    (productIso R q n h i j).hom).mp (overlap_closed R q n h i j)
instance scheme_separated : (scheme R q n h).IsSeparated := by
  have := separated R q n h
  constructor
  rw [← terminal.comp_from (toBase R q n h)]
  infer_instance
end FLT.Mazur.PolygonInfinitesimalSeparated
