/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNodeIncidence
public import FLT.Mazur.PolygonNodeLocus
public import FLT.Mazur.PolygonSeparated
public import FLT.Mazur.PolygonTranslationImages

/-!
# Translation on the actual polygon incidence graph

Vertices are all irreducible components and edges are all nonsmooth points.
Their incidence is cyclic and the universal-action translations rotate both.
The statements include the loop when there is just one component.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.PolygonActionGraph
open PolygonPinching PolygonActionTranslation
variable (K : Type u) [Field K]
/-- The unique point of the coefficient field's spectrum. -/
def basePoint : Spec (.of K) := Classical.choice inferInstance
variable (n : ℕ) [NeZero n] (hn : 0 < n) {C : Over (Spec (.of K))}
  (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
/-- The vertices are the actual irreducible components. -/
def vertices : Fin n ≃ irreducibleComponents C.left :=
  PolygonComponentDistinct.equivalence K n hn p q h

variable [LocallyOfFinitePresentation C.hom]
/-- The edges are the actual nonsmooth points, hence actual nodes. -/
def edges : Fin n ≃ {x : C.left // x ∉ C.hom.smoothLocus} :=
  Equiv.ofBijective (fun j ↦ ⟨(nodeι K n j ≫ q).left (basePoint K),
    (PolygonNodeLocus.nonsmooth_iff K n hn p q h _).mpr ⟨j, basePoint K, rfl⟩⟩)
    ⟨fun i j he ↦ (PolygonNodeIncidence.node_eq_iff K n hn p q h i j _ _).mp
        (congrArg Subtype.val he), by
      rintro ⟨x, hx⟩
      obtain ⟨j, y, rfl⟩ := (PolygonNodeLocus.nonsmooth_iff K n hn p q h x).mp hx
      exact ⟨j, Subtype.ext (congrArg (nodeι K n j ≫ q).left
        (show basePoint K = y from Subsingleton.elim _ _))⟩⟩

/-- Incidence on the actual components and nodes is the cyclic graph, with a loop for n=1. -/
theorem incidence (i j : Fin n) :
    (edges K n hn p q h j).val ∈ (vertices K n hn p q h i).val ↔
      i = j ∨ i = next hn j :=
  PolygonNodeIncidence.incidence K n hn p q h i j (basePoint K)

omit [LocallyOfFinitePresentation C.hom] in
/-- Translation rotates the actual irreducible components. -/
theorem vertex_translation (a : Kˣ) (b : ZMod n) (i : Fin n) :
    (translation K n hn p q h a b).left '' (vertices K n hn p q h i).val =
      (vertices K n hn p q h (rotateIndex b i)).val :=
  PolygonTranslationImages.component_image K n hn p q h a b i

/-- Translation rotates the actual node points. -/
theorem edge_translation (a : Kˣ) (b : ZMod n) (j : Fin n) :
    (translation K n hn p q h a b).left (edges K n hn p q h j).val =
      (edges K n hn p q h (rotateIndex b j)).val :=
  congrArg (fun f ↦ f.left (basePoint K)) (node_translation K n hn p q h a b j)

/-- Both ends rotate together, preserving actual incidence, also for one and two components. -/
theorem rotation_incidence (b : ZMod n) (i j : Fin n) :
    (edges K n hn p q h (rotateIndex b j)).val ∈
      (vertices K n hn p q h (rotateIndex b i)).val ↔
    (edges K n hn p q h j).val ∈ (vertices K n hn p q h i).val := by
  rw [incidence, incidence, ← rotateIndex_next]
  have hi : Function.Injective (rotateIndex b : Fin n → Fin n) := by
    intro i j he
    apply (ZMod.finEquiv n).injective
    exact add_right_cancel ((ZMod.finEquiv n).symm.injective he)
  exact or_congr hi.eq_iff hi.eq_iff

/-- Every graph edge satisfies the actual completed-stalk node criterion. -/
theorem edge_isNode (j : Fin n) :
    FCurve.CurveNode.IsNode C.hom (edges K n hn p q h j).val := by
  let := PolygonSeparated.cocone K n hn p q h
  let f := nodeι K n j ≫ q
  have hf : IsClosedImmersion (f.left ≫ C.hom) := by
    rw [f.w]
    change IsClosedImmersion (𝟙 (Spec (.of K)))
    infer_instance
  have : IsClosedImmersion f.left := IsClosedImmersion.of_comp f.left C.hom
  have he : Set.range f.left = {(edges K n hn p q h j).val} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact congrArg f.left (Subsingleton.elim (α := Spec (.of K)) y (basePoint K))
    · rintro rfl
      exact ⟨basePoint K, rfl⟩
  have hc := f.left.isClosedEmbedding.isClosed_range
  rw [he] at hc
  rcases PolygonNodalCore.nodes K n hn p q h _ hc with hs | hn
  · exact ((edges K n hn p q h j).property hs).elim
  · exact hn
end FLT.Mazur.PolygonActionGraph
