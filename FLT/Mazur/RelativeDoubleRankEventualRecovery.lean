/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDoubleRankTransitions

/-!
# Eventual full recovery of compact independent-rank tests

A compact test with two fixed ranks factors at every sufficiently high pair
of orders, uniquely and compatibly. When the test is the coefficient scheme,
the full rank maps are eventually isomorphisms. No reduction of the test is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B T : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (x y : B ⟶ S) (n m : ℕ)

/-- Any full test factorization extends canonically to larger independent orders. -/
def doubleRankExtend {r s r' s' : ℕ} (hr : r ≤ r') (hs : s ≤ s')
    (g : T ⟶ doubleRankThickening E x y n m r s) :
    T ⟶ doubleRankThickening E x y n m r' s' :=
  g ≫ doubleRankTransition E x y n m hr hs

/-- The extended factorization still has exactly the original coefficient map. -/
@[reassoc (attr := simp)]
theorem doubleRankExtend_map {r s r' s' : ℕ} (hr : r ≤ r') (hs : s ≤ s')
    (g : T ⟶ doubleRankThickening E x y n m r s) :
    doubleRankExtend E x y n m hr hs g ≫ doubleRankMap E x y n m r' s' =
      g ≫ doubleRankMap E x y n m r s := by
  rw [doubleRankExtend, Category.assoc, doubleRankTransition_map]

/-- Every pair of full factorizations is compatible with the actual order transition. -/
theorem doubleRank_factors_compatible {r s r' s' : ℕ} (hr : r ≤ r') (hs : s ≤ s')
    (v : T ⟶ B) (g : T ⟶ doubleRankThickening E x y n m r s)
    (g' : T ⟶ doubleRankThickening E x y n m r' s')
    (hg : g ≫ doubleRankMap E x y n m r s = v)
    (hg' : g' ≫ doubleRankMap E x y n m r' s' = v) :
    g ≫ doubleRankTransition E x y n m hr hs = g' := by
  apply (cancel_mono (doubleRankMap E x y n m r' s')).mp
  rw [Category.assoc, doubleRankTransition_map, hg, hg']

variable [IsNoetherian S]

/-- One bound gives unique full factorizations at every later independent pair of orders. -/
theorem exists_eventual_doubleRank_factor [CompactSpace T] (v : T ⟶ B)
    (hx : Set.range (v ≫ x) ⊆ exactRank E n)
    (hy : Set.range (v ≫ y) ⊆ exactRank E m) :
    ∃ k : ℕ, ∀ r s : ℕ, k ≤ r → k ≤ s →
      ∃! g : T ⟶ doubleRankThickening E x y n m r s,
        g ≫ doubleRankMap E x y n m r s = v := by
  obtain ⟨r₀, s₀, g, hg⟩ := exists_doubleRank_factor E x y n m v hx hy
  refine ⟨max r₀ s₀, fun r s hr hs ↦ ?_⟩
  let d := doubleRankExtend E x y n m ((le_max_left _ _).trans hr)
    ((le_max_right _ _).trans hs) g
  have hd : d ≫ doubleRankMap E x y n m r s = v := by
    exact (doubleRankExtend_map E x y n m _ _ g).trans hg
  exact ⟨d, hd, fun d' hd' ↦ (cancel_mono _).mp (hd'.trans hd.symm)⟩

/-- Fixed endpoint ranks recover the entire compact coefficient scheme at all later orders. -/
theorem exists_eventual_doubleRankMap_isIso [CompactSpace B]
    (hx : Set.range x ⊆ exactRank E n) (hy : Set.range y ⊆ exactRank E m) :
    ∃ k : ℕ, ∀ r s : ℕ, k ≤ r → k ≤ s → IsIso (doubleRankMap E x y n m r s) := by
  obtain ⟨k, hk⟩ := exists_eventual_doubleRank_factor E x y n m (𝟙 B)
    (by simpa using hx) (by simpa using hy)
  refine ⟨k, fun r s hr hs ↦ ?_⟩
  obtain ⟨g, hg, _⟩ := hk r s hr hs
  refine ⟨g, ?_, hg⟩
  apply (cancel_mono (doubleRankMap E x y n m r s)).mp
  rw [Category.assoc, hg, Category.comp_id, Category.id_comp]

end FLT.Mazur.RelativeOrderedTuples
