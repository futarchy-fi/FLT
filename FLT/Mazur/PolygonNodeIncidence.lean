/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonComponentDistinct
public import FLT.Mazur.PolygonNodesClosed
public import FLT.Mazur.PolygonCyclicNormalizationRanges

/-!
# Actual node/component incidence of the polygon

The two specified endpoints lie on adjacent irreducible components, and the
cyclic normalization chart excludes every other component. Distinct node
indices give distinct points, including in the two-gon.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.PolygonNodeIncidence
open PolygonPinching
variable (K : Type u) [Field K]

/-- No component other than the two adjacent components contains a cyclic node. -/
theorem cyclic_incidence (n : ℕ) (hn : 2 ≤ n) (i j : Fin n) (x : Spec (.of K))
    (z : ProjectiveLine.scheme K)
    (he : PolygonCyclicAtlas.componentMap K n hn i z =
      (PolygonNodePresentation.aOrigin K ≫ PolygonCyclicAtlas.chart K n hn j) x) :
    i = j ∨ i = finRotate n j := by
  rcases PolygonCyclicNormalizationRanges.component_preimage K n hn i j z
    ⟨PolygonNodePresentation.aOrigin K x, he.symm⟩ with ⟨_, hi, _⟩ | ⟨_, hi, _⟩
  · exact Or.inl hi
  · exact Or.inr hi

variable (n : ℕ) [NeZero n] (hn : 0 < n) {C : Over (Spec (.of K))}
  (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
omit [NeZero n] in
include h in
@[reassoc] theorem zero_node (j : Fin n) :
    ProjectiveLine.zeroSection K ≫ componentι K n j ≫ p = nodeι K n j ≫ q := by
  have he := congrArg (fun f ↦ branchι K n j false ≫ f) h.w
  simpa only [← Category.assoc, branchι_toComponents_zero, branchι_toNodes] using he
omit [NeZero n] in
include h in
@[reassoc] theorem infinity_node (j : Fin n) :
    ProjectiveLine.infinitySection K ≫ componentι K n (next hn j) ≫ p = nodeι K n j ≫ q := by
  have he := congrArg (fun f ↦ branchι K n j true ≫ f) h.w
  simpa only [← Category.assoc, branchι_toComponents_infinity, branchι_toNodes] using he

include h in
/-- Actual membership in an irreducible component is exactly cyclic adjacency. -/
theorem incidence (i j : Fin n) (x : Spec (.of K)) :
    (nodeι K n j ≫ q).left x ∈ Set.range (componentι K n i ≫ p).left ↔
      i = j ∨ i = next hn j := by
  constructor
  · rintro ⟨z, hz⟩
    rcases n with _ | (_ | m)
    · exact (NeZero.ne 0 rfl).elim
    · exact Or.inl (Fin.ext (by omega))
    · let e := (polygonIso K (m + 2) hn p q h).symm ≪≫
        PolygonAtlas.cyclicIso K (m + 2) (by omega)
      have he := congrArg (fun y ↦ e.hom.left y) hz
      change ((componentι K (m + 2) i ≫ p) ≫ e.hom).left z =
        ((nodeι K (m + 2) j ≫ q) ≫ e.hom).left x at he
      simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
        normalization_polygonIso_inv_assoc, nodes_polygonIso_inv_assoc,
        PolygonAtlas.normalization_cyclicIso, PolygonAtlas.nodes_cyclicIso,
        PolygonCyclicAtlas.componentι_normalization, PolygonCyclicAtlas.nodeι_nodes] at he
      rw [PolygonCyclicAtlas.next_eq_rotate]
      exact cyclic_incidence K (m + 2) (by omega) i j x z he
  · rintro (hi | hi) <;> subst i
    · exact ⟨(ProjectiveLine.zeroSection K).left x,
        congrArg (fun f ↦ f.left x) (zero_node K n hn p q h j)⟩
    · exact ⟨(ProjectiveLine.infinitySection K).left x,
        congrArg (fun f ↦ f.left x) (infinity_node K n hn p q h j)⟩
include h in
/-- Distinct specified nodes are distinct points of the actual polygon. -/
theorem node_eq_iff (i j : Fin n) (x y : Spec (.of K)) :
    (nodeι K n i ≫ q).left x = (nodeι K n j ≫ q).left y ↔ i = j := by
  let := PolygonNodesClosed.cocone K n hn p q h
  constructor
  · intro he
    have he' := q.left.isClosedEmbedding.injective he
    change (nodeι K n i).left x = (nodeι K n j).left y at he'
    let c := sigmaComparison (Over.forget (Spec (.of K)))
      (fun _ : Fin n ↦ point K)
    have hi (k : Fin n) : Sigma.ι (fun _ : Fin n ↦ Spec (.of K)) k ≫ c =
        (nodeι K n k).left :=
      ι_comp_sigmaComparison (Over.forget _) (fun _ : Fin n ↦ point K) k
    have hc : c (Sigma.ι (fun _ : Fin n ↦ Spec (.of K)) i x) =
        c (Sigma.ι (fun _ : Fin n ↦ Spec (.of K)) j y) := by
      change (Sigma.ι (fun _ : Fin n ↦ Spec (.of K)) i ≫ c) x =
        (Sigma.ι (fun _ : Fin n ↦ Spec (.of K)) j ≫ c) y
      rw [hi, hi]
      exact he'
    have hh := c.isOpenEmbedding.injective hc
    exact congrArg Sigma.fst ((sigmaι_eq_iff (fun _ : Fin n ↦ Spec (.of K)) i j x y).mp hh)
  · rintro rfl
    exact congrArg (nodeι K n i ≫ q).left (show x = y from Subsingleton.elim x y)

end FLT.Mazur.PolygonNodeIncidence
