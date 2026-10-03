/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonComponentImages
/-!
# Connectedness of the polygon

Each normalization image is connected. The two endpoints at every node
make consecutive images intersect, so the entire polygon is connected.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.PolygonConnected
open PolygonPinching
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
include h in
omit [NeZero n] in
theorem adjacent (i : Fin n) :
    (Set.range (componentι K n i ≫ p).left ∩
      Set.range (componentι K n (next hn i) ≫ p).left).Nonempty := by
  have hzero : ProjectiveLine.zeroSection K ≫ componentι K n i ≫ p = nodeι K n i ≫ q := by
    rw [← branchι_toComponents_zero_assoc K n hn i p, h.w, branchι_toNodes_assoc]
  have hinf : ProjectiveLine.infinitySection K ≫ componentι K n (next hn i) ≫ p =
      nodeι K n i ≫ q := by
    rw [← branchι_toComponents_infinity_assoc K n hn i p, h.w, branchι_toNodes_assoc]
  let z : Spec (.of K) := Classical.choice inferInstance
  refine ⟨(nodeι K n i ≫ q).left z, ?_, ?_⟩
  · refine ⟨ProjectiveLine.zero K z, ?_⟩
    exact congrArg (fun f ↦ f.left z) hzero
  · refine ⟨ProjectiveLine.infinity K z, ?_⟩
    exact congrArg (fun f ↦ f.left z) hinf
include h in
theorem connected : ConnectedSpace C.left := by
  let s : ℕ → Set C.left := fun j ↦ Set.range (componentι K n ⟨j % n, Nat.mod_lt _ hn⟩ ≫ p).left
  have hs : ∀ j, _root_.IsConnected (s j) := fun j ↦
    (PolygonComponentImages.mem_components K n hn p q h _).1.isConnected
  have ha : ∀ j, (s j ∩ s (Order.succ j)).Nonempty := by
    intro j
    have he : next hn ⟨j % n, Nat.mod_lt _ hn⟩ = ⟨(j + 1) % n, Nat.mod_lt _ hn⟩ := by
      apply Fin.ext
      simp only [next_val, Nat.add_mod, Nat.mod_mod]
    simpa only [s, Order.succ_eq_add_one, ← he] using adjacent K n hn p q h ⟨j % n, Nat.mod_lt _ hn⟩
  have hc := _root_.IsConnected.iUnion_of_chain hs ha
  have hu : (⋃ j, s j) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, y, rfl⟩ := PolygonComponentImages.cover K n hn p q h x
    apply Set.mem_iUnion.mpr
    refine ⟨i.val, ?_⟩
    simpa only [s, Nat.mod_eq_of_lt i.isLt] using Set.mem_range_self y
  rw [hu] at hc
  exact connectedSpace_iff_univ.mpr hc
end FLT.Mazur.PolygonConnected
