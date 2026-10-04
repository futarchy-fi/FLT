/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCubicGenerationCover
public import FLT.Mazur.PolygonNormalizationTorusPullback

/-!
# Node charts in the specified polygon cocone

Transport the actual split and one-gon affine charts to the supplied pinching
cocone. Their origins are precisely its specified nodes, and these origins
avoid every marked divisor point.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonNodeAffineCharts
open PolygonPinching PolygonNodePresentation PolygonCubicSections
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

include h in
/-- Every specified node avoids the actual marked divisor support. -/
lemma node_mem_complement (a : Fin n → Kˣ) (i : Fin n) (x : Spec (.of K)) :
    (nodeι K n i ≫ q).left x ∈ divisorComplement K n p a := by
  intro hx
  obtain ⟨j, y, hy⟩ :=
    (PolygonBoundaryDivisor.mem_support_iff K n p hn q h a _).mp hx
  have ht := PolygonMarkedSections.section_mem_torus K n p (a j) j y
  rw [hy] at ht
  exact PolygonNormalizationTorusPullback.node_not_torus K n hn p q h j i x ht

/-- The split-node affine chart transported to the specified cocone. -/
def splitChart (hn₂ : 2 ≤ n) (i : Fin n) : PolygonNodeBranches.node K ⟶ C.left :=
  PolygonCyclicAtlas.chart K n hn₂ i ≫
    (PolygonAtlas.cyclicIso K n hn₂).inv.left ≫ (polygonIso K n hn p q h).hom.left

instance splitChart_isOpenImmersion (hn₂ : 2 ≤ n) (i : Fin n) :
    IsOpenImmersion (splitChart K n hn p q h hn₂ i) := by
  have : IsIso (PolygonAtlas.cyclicIso K n hn₂).inv.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (PolygonAtlas.cyclicIso K n hn₂).inv))
  have : IsIso (polygonIso K n hn p q h).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (polygonIso K n hn p q h).hom))
  unfold splitChart
  infer_instance

/-- The chart origin retains its exact cyclic index, also when n = 2. -/
@[reassoc]
lemma splitChart_origin (hn₂ : 2 ≤ n) (i : Fin n) :
    aOrigin K ≫ splitChart K n hn p q h hn₂ i = (nodeι K n i ≫ q).left := by
  unfold splitChart
  rw [← Category.assoc, ← PolygonAtlas.cyclic_node]
  change ((nodeι K n i ≫ PolygonAtlas.nodes K n ≫
    (PolygonAtlas.cyclicIso K n hn₂).hom) ≫
    (PolygonAtlas.cyclicIso K n hn₂).inv ≫ (polygonIso K n hn p q h).hom).left = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc, nodes_polygonIso]

/-- The split chart origin lies in the true canonical-denominator open. -/
lemma splitChart_origin_mem (a : Fin n → Kˣ) (hn₂ : 2 ≤ n)
    (i : Fin n) (x : Spec (.of K)) :
    splitChart K n hn p q h hn₂ i (aOrigin K x) ∈ divisorComplement K n p a := by
  change (aOrigin K ≫ splitChart K n hn p q h hn₂ i) x ∈ _
  rw [splitChart_origin]
  exact node_mem_complement K n hn p q h a i x

end PolygonNodeAffineCharts

namespace PolygonNodeAffineCharts
open PolygonPinching PolygonNodePresentation PolygonCubicSections
variable (K : Type u) [Field K] (hn : 0 < 1)
  {C : Over (Spec (.of K))} (p : components K 1 ⟶ C) (q : nodes K 1 ⟶ C)
  (h : IsPushout (toComponents K 1 hn) (toNodes K 1) p q)

/-- The actual B-chart of the one-gon transported to the specified cocone. -/
def oneChart : OneGonGluing.nodeChart K ⟶ C.left :=
  OneGonGluing.node K ≫ (polygonIso K 1 hn p q h).hom.left

instance oneChart_isOpenImmersion : IsOpenImmersion (oneChart K hn p q h) := by
  have : IsIso (polygonIso K 1 hn p q h).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (polygonIso K 1 hn p q h).hom))
  unfold oneChart
  infer_instance

/-- The one-gon chart keeps the identified endpoints as its actual node. -/
@[reassoc]
lemma oneChart_origin (i : Fin 1) :
    bOrigin K ≫ oneChart K hn p q h = (nodeι K 1 i ≫ q).left := by
  unfold oneChart
  rw [← Category.assoc, ← OneGonNormalization.nodeι_nodes K i]
  change ((nodeι K 1 i ≫ PolygonAtlas.nodes K 1) ≫
    (polygonIso K 1 hn p q h).hom).left = _
  simp only [Category.assoc, nodes_polygonIso]

/-- The self-pinched node avoids the marked point. -/
lemma oneChart_origin_mem (a : Fin 1 → Kˣ) (i : Fin 1) (x : Spec (.of K)) :
    oneChart K hn p q h (bOrigin K x) ∈ divisorComplement K 1 p a := by
  change (bOrigin K ≫ oneChart K hn p q h) x ∈ _
  rw [oneChart_origin K hn p q h i]
  exact node_mem_complement K 1 hn p q h a i x

end FLT.Mazur.PolygonNodeAffineCharts
