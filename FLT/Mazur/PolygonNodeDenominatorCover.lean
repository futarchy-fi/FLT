/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOneGonDenominator
public import FLT.Mazur.PolygonSplitNodeDenominator

/-!
# The refined node charts and torus charts cover the polygon

Every smooth point lies in a torus chart. Every other point is a specified
node, and the principal refinement of its actual node chart retains it.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonNodeAffineCharts
open PolygonPinching PolygonCubicSections
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- The refined split-node charts together with the tori cover every polygon with n ≥ 2. -/
lemma splitDenominator_covers (a : Fin n → Kˣ) (hn₂ : 2 ≤ n) (z : C.left) :
    (∃ i, z ∈ torusOpen K n hn p q h i) ∨
      ∃ i x, z ∈ Set.range (splitDenominatorChart K n hn p q h a hn₂ i x) := by
  let := polygon_lfp K n hn p q h
  by_cases hz : z ∈ C.hom.smoothLocus
  · change z ∈ (C.hom.smoothLocus : Set C.left) at hz
    rw [smooth_range K n hn p q h] at hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    exact Or.inl ⟨i, hi⟩
  · obtain ⟨i, x, rfl⟩ := (PolygonNodeLocus.nonsmooth_iff K n hn p q h z).mp hz
    exact Or.inr ⟨i, x, splitDenominatorChart_node_mem K n hn p q h a hn₂ i x⟩

end PolygonNodeAffineCharts
namespace PolygonNodeAffineCharts
open PolygonPinching PolygonCubicSections
variable (K : Type u) [Field K] (hn : 0 < 1)
  {C : Over (Spec (.of K))} (p : components K 1 ⟶ C) (q : nodes K 1 ⟶ C)
  (h : IsPushout (toComponents K 1 hn) (toNodes K 1) p q)

/-- The refined B-chart and the torus cover the self-pinched one-gon. -/
lemma oneDenominator_covers (a : Fin 1 → Kˣ) (z : C.left) :
    (∃ i, z ∈ torusOpen K 1 hn p q h i) ∨
      ∃ x, z ∈ Set.range (oneDenominatorChart K hn p q h a x) := by
  let := polygon_lfp K 1 hn p q h
  by_cases hz : z ∈ C.hom.smoothLocus
  · change z ∈ (C.hom.smoothLocus : Set C.left) at hz
    rw [smooth_range K 1 hn p q h] at hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    exact Or.inl ⟨i, hi⟩
  · obtain ⟨i, x, rfl⟩ := (PolygonNodeLocus.nonsmooth_iff K 1 hn p q h z).mp hz
    exact Or.inr ⟨x, oneDenominatorChart_node_mem K hn p q h a x i⟩

end FLT.Mazur.PolygonNodeAffineCharts
