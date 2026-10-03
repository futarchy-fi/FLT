/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNodalCore
public import FLT.Mazur.PolygonNodesClosed
public import FLT.Mazur.PolygonSmoothLocus

/-!
# The actual nonsmooth locus of the polygon

The local node origin is the unique nonsmooth point of each node chart.
The chart covers and the specified cocone identify all nonsmooth points
with the prescribed node images, including the irreducible one-gon.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.PolygonNodeLocus
open PolygonPinching PolygonNodePresentation
variable (K : Type u) [Field K]

theorem cyclic_not_smooth (n : ℕ) (hn : 2 ≤ n) (j : Fin n) (x : Spec (.of K)) :
    let := cyclic_lfp K n hn
    (aOrigin K ≫ PolygonCyclicAtlas.chart K n hn j) x ∉
      (PolygonCyclicAtlas.toBase K n hn).smoothLocus := by
  let := cyclic_lfp K n hn
  dsimp only
  intro hx
  have he := (PolygonAtlas.mem_smooth_iff (PolygonCyclicAtlas.chart K n hn j)
    (PolygonCyclicAtlas.toBase K n hn) (aOrigin K x)).mp hx
  simp only [PolygonCyclicAtlas.chart_toBase] at he
  change aOrigin K x ∈ ((aToBase K).smoothLocus : Set _) at he
  rw [a_smooth_complement] at he
  exact he ⟨x, rfl⟩

theorem one_not_smooth (x : Spec (.of K)) : let := oneGon_lfp K
    (bOrigin K ≫ OneGonGluing.node K) x ∉ (OneGonGluing.toBase K).smoothLocus := by
  let := oneGon_lfp K
  dsimp only
  intro hx
  have he := (PolygonAtlas.mem_smooth_iff (OneGonGluing.node K)
    (OneGonGluing.toBase K) (bOrigin K x)).mp hx
  simp only [OneGonGluing.node_toBase] at he
  change bOrigin K x ∈ ((bToBase K).smoothLocus : Set _) at he
  rw [b_smooth_complement] at he
  exact he ⟨x, rfl⟩

theorem atlas_node_not_smooth (n : ℕ) [NeZero n] (j : Fin n) (x : Spec (.of K)) :
    (nodeι K n j ≫ PolygonAtlas.nodes K n).left x ∉ (PolygonAtlas.polygon K n).hom.smoothLocus := by
  rcases n with _ | (_ | m)
  · exact (NeZero.ne 0 rfl).elim
  · let := oneGon_lfp K
    change (nodeι K 1 j ≫ OneGonNormalization.nodes K).left x ∉
      (OneGonGluing.toBase K).smoothLocus
    rw [OneGonNormalization.nodeι_nodes]
    exact one_not_smooth K x
  · let := cyclic_lfp K (m + 2) (by omega)
    change (nodeι K (m + 2) j ≫ PolygonCyclicAtlas.nodes K (m + 2) _).left x ∉
      (PolygonCyclicAtlas.toBase K (m + 2) _).smoothLocus
    rw [PolygonCyclicAtlas.nodeι_nodes]
    exact cyclic_not_smooth K (m + 2) (by omega) j x

theorem cyclic_nonsmooth_cover (n : ℕ) (hn : 2 ≤ n)
    (z : PolygonCyclicAtlas.scheme K n hn)
    (hz : let := cyclic_lfp K n hn
      z ∉ (PolygonCyclicAtlas.toBase K n hn).smoothLocus) :
    ∃ j x, (nodeι K n j ≫ PolygonCyclicAtlas.nodes K n hn).left x = z := by
  let := cyclic_lfp K n hn
  obtain ⟨j, y, rfl⟩ := PolygonCyclicAtlas.charts_cover K n hn z
  have he := mt (PolygonAtlas.mem_smooth_iff (PolygonCyclicAtlas.chart K n hn j)
    (PolygonCyclicAtlas.toBase K n hn) y).mpr hz
  simp only [PolygonCyclicAtlas.chart_toBase] at he
  change y ∉ ((aToBase K).smoothLocus : Set _) at he
  rw [a_smooth_complement, Set.mem_compl_iff, not_not] at he
  obtain ⟨x, rfl⟩ := he
  exact ⟨j, x, congrArg (fun f ↦ f x) (PolygonCyclicAtlas.nodeι_nodes K n hn j)⟩

theorem one_nonsmooth_cover (z : OneGonGluing.scheme K)
    (hz : let := oneGon_lfp K
      z ∉ (OneGonGluing.toBase K).smoothLocus) :
    ∃ x, (bOrigin K ≫ OneGonGluing.node K) x = z := by
  let := oneGon_lfp K
  rcases OneGonGluing.charts_cover K z with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · have he := mt (PolygonAtlas.mem_smooth_iff (OneGonGluing.node K)
      (OneGonGluing.toBase K) y).mpr hz
    simp only [OneGonGluing.node_toBase] at he
    change y ∉ ((bToBase K).smoothLocus : Set _) at he
    rw [b_smooth_complement, Set.mem_compl_iff, not_not] at he
    obtain ⟨x, rfl⟩ := he
    exact ⟨x, rfl⟩
  · exact (hz (by
      apply (PolygonAtlas.mem_smooth_iff (OneGonGluing.torus K) _ y).mpr
      have : Smooth (OneGonGluing.torusToBase K) := by
        change Smooth (MultiplicativeGroupScheme.gm K).hom
        infer_instance
      have he : y ∈ (OneGonGluing.torusToBase K).smoothLocus := by
        rw [Scheme.Hom.smoothLocus_eq_top]
        trivial
      simpa only [OneGonGluing.torus_toBase] using he)).elim

theorem atlas_nonsmooth_cover (n : ℕ) [NeZero n] (z : (PolygonAtlas.polygon K n).left)
    (hz : z ∉ (PolygonAtlas.polygon K n).hom.smoothLocus) :
    ∃ j x, (nodeι K n j ≫ PolygonAtlas.nodes K n).left x = z := by
  rcases n with _ | (_ | m)
  · exact (NeZero.ne 0 rfl).elim
  · obtain ⟨x, hx⟩ := one_nonsmooth_cover K z hz
    exact ⟨0, x, (congrArg (fun f ↦ f x) (OneGonNormalization.nodeι_nodes K 0)).trans hx⟩
  · exact cyclic_nonsmooth_cover K (m + 2) (by omega) z hz

variable (n : ℕ) [NeZero n] (hn : 0 < n) {C : Over (Spec (.of K))}
  (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
include h in
/-- The actual nonsmooth points are exactly the specified node images. -/
theorem nonsmooth_iff [LocallyOfFinitePresentation C.hom] (z : C.left) :
    z ∉ C.hom.smoothLocus ↔ ∃ j x, (nodeι K n j ≫ q).left x = z := by
  let e := (Over.forget _).mapIso (polygonIso K n hn p q h)
  obtain ⟨y, rfl⟩ := e.hom.homeomorph.surjective z
  have he : e.hom y ∈ C.hom.smoothLocus ↔
      y ∈ (PolygonAtlas.polygon K n).hom.smoothLocus := by
    simpa only [e, Functor.mapIso_hom, Over.forget_map, Over.w] using
      PolygonAtlas.mem_smooth_iff e.hom C.hom y
  change e.hom y ∉ C.hom.smoothLocus ↔ ∃ j x, (nodeι K n j ≫ q).left x = e.hom y
  rw [he]
  have hf (j : Fin n) (x : Spec (.of K)) :
      e.hom ((nodeι K n j ≫ PolygonAtlas.nodes K n).left x) =
        (nodeι K n j ≫ q).left x := by
    change ((nodeι K n j ≫ PolygonAtlas.nodes K n) ≫ (polygonIso K n hn p q h).hom).left x = _
    simp only [Category.assoc, nodes_polygonIso]
  constructor
  · intro hy
    obtain ⟨j, x, rfl⟩ := atlas_nonsmooth_cover K n y hy
    exact ⟨j, x, (hf j x).symm⟩
  · rintro ⟨j, x, hx⟩
    have hh := e.hom.isOpenEmbedding.injective ((hf j x).trans hx)
    rw [← hh]
    exact atlas_node_not_smooth K n j x
end FLT.Mazur.PolygonNodeLocus
