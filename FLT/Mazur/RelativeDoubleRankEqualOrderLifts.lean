/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDoubleRankTransitions
public import FLT.Mazur.RelativeDoubleRankGlobalLifts

/-!
# Full comparison lifts from equal infinitesimal orders

Actual order transitions restrict a comparison arrow at a sufficiently high
equal order to any prescribed independent orders. Closed comparison detection
then constructs a whole-scheme arrow. Both ranks remain independent.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B Z Y : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (x y : B ⟶ S)

/-- Full comparison arrows restrict from a common higher order to independent lower orders. -/
theorem doubleRank_lifts_iff_equal_orders (n m : ℕ) (c : Z ⟶ Y) (t : B ⟶ Y) :
    (∀ r s : ℕ, ∃ d : doubleRankThickening E x y n m r s ⟶ Z,
      d ≫ c = doubleRankMap E x y n m r s ≫ t) ↔
    ∀ k : ℕ, ∃ d : doubleRankThickening E x y n m k k ⟶ Z,
      d ≫ c = doubleRankMap E x y n m k k ≫ t := by
  refine ⟨fun h k ↦ h k k, fun h r s ↦ ?_⟩
  obtain ⟨d, hd⟩ := h (max r s)
  refine ⟨doubleRankTransition E x y n m (le_max_left r s) (le_max_right r s) ≫ d, ?_⟩
  rw [Category.assoc, hd, doubleRankTransition_map_assoc]

/-- A tail of equal orders suffices; low-order arrows are constructed by restriction. -/
theorem doubleRank_lifts_of_equal_order_tail (n m k₀ : ℕ) (c : Z ⟶ Y) (t : B ⟶ Y)
    (h : ∀ k : ℕ, k₀ ≤ k → ∃ d : doubleRankThickening E x y n m k k ⟶ Z,
      d ≫ c = doubleRankMap E x y n m k k ≫ t) (r s : ℕ) :
    ∃ d : doubleRankThickening E x y n m r s ⟶ Z,
      d ≫ c = doubleRankMap E x y n m r s ≫ t := by
  let k := max k₀ (max r s)
  obtain ⟨d, hd⟩ := h k (le_max_left _ _)
  refine ⟨doubleRankTransition E x y n m
    ((le_max_left r s).trans (le_max_right k₀ _))
    ((le_max_right r s).trans (le_max_right k₀ _)) ≫ d, ?_⟩
  rw [Category.assoc, hd, doubleRankTransition_map_assoc]

variable [IsNoetherian S] [QuasiCompact E.hom] [IsLocallyNoetherian B]

/-- Equal-order arrows detect the entire closed comparison on a full coefficient scheme. -/
theorem existsUnique_global_lift_of_equal_orders (c : Z ⟶ Y) [Mono c] (t : B ⟶ Y)
    [IsClosedImmersion (pullback.snd c t)]
    (h : ∀ n m k : ℕ, ∃ d : doubleRankThickening E x y n m k k ⟶ Z,
      d ≫ c = doubleRankMap E x y n m k k ≫ t) :
    ∃! d : B ⟶ Z, d ≫ c = t := by
  apply existsUnique_global_lift_of_doubleRank E x y c t
  exact fun n m ↦ (doubleRank_lifts_iff_equal_orders E x y n m c t).mpr (h n m)

/-- Independent ranks can have different starting orders for their full comparison arrows. -/
theorem existsUnique_global_lift_of_equal_order_tails (c : Z ⟶ Y) [Mono c] (t : B ⟶ Y)
    [IsClosedImmersion (pullback.snd c t)]
    (h : ∀ n m : ℕ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ d : doubleRankThickening E x y n m k k ⟶ Z,
        d ≫ c = doubleRankMap E x y n m k k ≫ t) :
    ∃! d : B ⟶ Z, d ≫ c = t := by
  apply existsUnique_global_lift_of_doubleRank E x y c t
  intro n m r s
  obtain ⟨k₀, hk₀⟩ := h n m
  exact doubleRank_lifts_of_equal_order_tail E x y n m k₀ c t hk₀ r s

end FLT.Mazur.RelativeOrderedTuples
