/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDoubleRankExactDenominators

/-!
# A fixed finite rank rectangle for the entire two-order tower

The rank rectangle can be chosen once, independently of both infinitesimal
orders. Exact powers and denominators still depend on the orders. This
distinction retains the full coefficient equations without asserting an
unjustified uniform annihilator of the infinite tower.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.RelativeOrderedTuples
open SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A T : Scheme.{0}} (E : Over A) [Etale E.hom] [IsSeparated E.hom]
  (x y : T ⟶ A) {R : Type} [CommRing R] (σ : R →+* Γ(T, ⊤))
  [NoetherianSpace A] [CompactSpace T]

/-- Every finite rectangle has an order-independent radical, but not necessarily exact kernel. -/
theorem doubleRankCollisionKernel_radical_order_independent (N r s r' s' : ℕ) :
    (doubleRankCollisionKernel E x y σ N r s).radical =
      (doubleRankCollisionKernel E x y σ N r' s').radical := by
  rw [doubleRankCollisionKernel_radical, doubleRankCollisionKernel_radical]
  apply iInf_congr
  intro n
  apply iInf_congr
  intro m
  apply iInf_congr
  intro hnm
  exact doubleRankScalarKernel_radical_order_independent E x y σ
    n.val m.val r s r' s' hnm

variable [QuasiCompact E.hom]

/-- One geometric rank rectangle computes the full collision ideal at every two orders. -/
theorem exists_uniform_doubleRank_collision_rectangle :
    ∃ N : ℕ, ∀ r s : ℕ, rankCollisionIdeal E x y (scalarMorphism σ) =
      (doubleRankCollisionKernel E x y σ N r s).radical := by
  obtain ⟨N, hN⟩ := exists_rankCollisionIdeal_exact_kernel E x y σ 0 0
  exact ⟨N, fun r s ↦ hN.trans
    (doubleRankCollisionKernel_radical_order_independent E x y σ N 0 0 r s)⟩

/-- The rank bound is uniform in both orders and in the chosen original obstruction scalar. -/
theorem exists_uniform_doubleRank_power_rectangle :
    ∃ N : ℕ, ∀ a ∈ rankCollisionIdeal E x y (scalarMorphism σ),
      ∀ r s : ℕ, ∃ k : ℕ, ∀ n m : Fin (N + 1), n.val ≠ m.val →
        (doubleRankMap E x y n.val m.val r s).appTop (σ (a ^ k)) = 0 := by
  obtain ⟨N, hN⟩ := exists_uniform_doubleRank_collision_rectangle E x y σ
  refine ⟨N, fun a ha r s ↦ ?_⟩
  rw [hN r s] at ha
  obtain ⟨k, hk⟩ := ha
  exact ⟨k, (mem_doubleRankCollisionKernel E x y σ N r s _).mp hk⟩

/-- Safe primes have exact full-stage denominators in one fixed rank rectangle at all orders. -/
theorem exists_uniform_doubleRank_denominator_rectangle :
    ∃ N : ℕ, ∀ P : PrimeSpectrum R,
      ¬ rankCollisionIdeal E x y (scalarMorphism σ) ≤ P.asIdeal →
      ∀ r s : ℕ, ∃ a : R, a ∉ P.asIdeal ∧
        a ∈ doubleRankCollisionKernel E x y σ N r s ∧
        a ∈ rankCollisionIdeal E x y (scalarMorphism σ) := by
  obtain ⟨N, hN⟩ := exists_uniform_doubleRank_collision_rectangle E x y σ
  refine ⟨N, fun P hP r s ↦ ?_⟩
  rw [hN r s, P.isPrime.radical_le_iff] at hP
  obtain ⟨a, ha, haP⟩ := Set.not_subset.mp hP
  refine ⟨a, haP, ha, ?_⟩
  rw [hN r s]
  exact Ideal.le_radical ha

end FLT.Mazur.RelativeOrderedTuples
