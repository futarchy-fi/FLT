/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRankCollisionFinite
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Constructing one original denominator from finite rank-pair tests

A product combines independently chosen original scalar equations for the
finitely many unequal-rank pairs. Closedness of their actual scalar images
also turns a common-rank fiber into a common-rank principal neighborhood.
The closed-image hypothesis is explicit; a fiber alone does not suffice.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A T : Scheme.{0}} (E : Over A) [Etale E.hom] [IsSeparated E.hom]
  [QuasiCompact E.hom] (x y : T ⟶ A)
  {R : Type} [CommRing R] (s : T ⟶ Spec (.of R)) (N : ℕ)
  (hN : ∀ a : A, ∀ n : ℕ, a ∈ rankImageOpen E n → n ≤ N)

include hN

omit [QuasiCompact E.hom] in
/-- Multiply finite pairwise equations in the original scalar ring, keeping the chosen prime. -/
theorem exists_rankCollision_denominator_of_pair_equations (P : PrimeSpectrum R)
    (h : ∀ i : Fin (N + 1) × Fin (N + 1), ∃ r : R, r ∉ P.asIdeal ∧
      ∀ t ∈ rankPairLocus E x y i.1.val i.2.val, r ∈ (s t).asIdeal) :
    ∃ r : R, r ∉ P.asIdeal ∧ r ∈ rankCollisionIdeal E x y s := by
  classical
  choose c hcP hc using h
  let r : R := ∏ i, c i
  have hrP : r ∉ P.asIdeal := by
    simp only [r, Ideal.IsPrime.prod_mem_iff, Finset.mem_univ, true_and, not_exists]
    exact hcP
  refine ⟨r, hrP, ?_⟩
  rw [rankCollisionIdeal, PrimeSpectrum.mem_vanishingIdeal]
  rintro z ⟨t, ht, rfl⟩
  rw [rankCollision_eq_finite_union E x y N hN] at ht
  obtain ⟨n, ht⟩ := Set.mem_iUnion.mp ht
  obtain ⟨m, ht⟩ := Set.mem_iUnion.mp ht
  exact (s t).asIdeal.mem_of_dvd
    (Finset.dvd_prod_of_mem c (Finset.mem_univ (n, m))) (hc (n, m) t ht)

/-- Closed rank-pair images remove the closure obstruction using only the actual scalar fiber. -/
theorem rankCollisionIdeal_not_le_of_closed_pair_images (P : PrimeSpectrum R)
    (hclosed : ∀ n m : Fin (N + 1),
      IsClosed (s '' rankPairLocus E x y n.val m.val))
    (hfiber : ∀ t : T, s t = P →
      ∃ n, x t ∈ exactRank E n ∧ y t ∈ exactRank E n) :
    ¬ rankCollisionIdeal E x y s ≤ P.asIdeal := by
  intro hbad
  have hb : P ∈ closure (s '' rankCollision E x y) := by
    rw [← rankCollisionIdeal_zeroLocus]
    exact hbad
  rw [rankCollision_closure_finite E x y s N hN] at hb
  obtain ⟨n, hb⟩ := Set.mem_iUnion.mp hb
  obtain ⟨m, hb⟩ := Set.mem_iUnion.mp hb
  rw [(hclosed n m).closure_eq] at hb
  obtain ⟨t, ht, htP⟩ := hb
  exact (not_mem_rankCollision_iff E x y t).mpr (hfiber t htP) ⟨n.val, m.val, ht⟩

/-- The constructed principal neighborhood controls every pair above it, not just the center. -/
theorem exists_same_rank_principal_of_closed_pair_images (P : PrimeSpectrum R)
    (hclosed : ∀ n m : Fin (N + 1),
      IsClosed (s '' rankPairLocus E x y n.val m.val))
    (hfiber : ∀ t : T, s t = P →
      ∃ n, x t ∈ exactRank E n ∧ y t ∈ exactRank E n) :
    ∃ r : R, r ∉ P.asIdeal ∧
      ∀ t : T, s t ∈ PrimeSpectrum.basicOpen r →
        ∃ n, x t ∈ exactRank E n ∧ y t ∈ exactRank E n :=
  (rankCollisionIdeal_not_le_iff E x y s P).mp
    (rankCollisionIdeal_not_le_of_closed_pair_images E x y s N hN P hclosed hfiber)

end FLT.Mazur.RelativeOrderedTuples
