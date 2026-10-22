/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDoubleRankScalarKernels

/-!
# Exact denominators on a finite rectangle of independent ranks

One power kills all full off-diagonal coefficient sections at two prescribed
orders. A scalar prime outside the collision obstruction therefore has a
denominator in the exact intersection of kernels, not merely its radical.
The exponent is allowed to depend on the two orders.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.RelativeOrderedTuples
open SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem radical_finite_iInf {R : Type} [CommRing R] {ι : Type*} [Finite ι]
    (I : ι → Ideal R) : (⨅ i, I i).radical = ⨅ i, (I i).radical := by
  let _ := Fintype.ofFinite ι
  simpa only [Finset.inf_univ_eq_iInf, Ideal.radicalInfTopHom_apply, Function.comp_def]
    using map_finset_inf (Ideal.radicalInfTopHom (R := R)) Finset.univ I

variable {A T : Scheme.{0}} (E : Over A) [Etale E.hom] [IsSeparated E.hom]
  (x y : T ⟶ A) {R : Type} [CommRing R] (σ : R →+* Γ(T, ⊤))

/-- The exact equations on every off-diagonal full stage in a finite rank rectangle. -/
def doubleRankCollisionKernel (N r s : ℕ) : Ideal R :=
  ⨅ n : Fin (N + 1), ⨅ m : Fin (N + 1), ⨅ (_ : n.val ≠ m.val),
    doubleRankScalarKernel E x y σ n.val m.val r s

/-- Membership retains the full section equation on each unreduced stage. -/
theorem mem_doubleRankCollisionKernel (N r s : ℕ) (a : R) :
    a ∈ doubleRankCollisionKernel E x y σ N r s ↔
      ∀ n m : Fin (N + 1), n.val ≠ m.val →
        (doubleRankMap E x y n.val m.val r s).appTop (σ a) = 0 := by
  simp only [doubleRankCollisionKernel, Ideal.mem_iInf]
  rfl

/-- Finite intersection permits one exponent for the whole independent rank rectangle. -/
theorem doubleRankCollisionKernel_radical (N r s : ℕ) :
    (doubleRankCollisionKernel E x y σ N r s).radical =
      ⨅ n : Fin (N + 1), ⨅ m : Fin (N + 1), ⨅ (_ : n.val ≠ m.val),
        (doubleRankScalarKernel E x y σ n.val m.val r s).radical := by
  classical
  simp only [doubleRankCollisionKernel, radical_finite_iInf]
  apply iInf_congr
  intro n
  apply iInf_congr
  intro m
  by_cases h : n.val = m.val <;> simp [h]

variable [NoetherianSpace A] [CompactSpace T] [QuasiCompact E.hom]

/-- At any fixed orders, one exact scalar ideal computes the complete collision obstruction. -/
theorem exists_rankCollisionIdeal_exact_kernel (r s : ℕ) :
    ∃ N : ℕ, rankCollisionIdeal E x y (scalarMorphism σ) =
      (doubleRankCollisionKernel E x y σ N r s).radical := by
  obtain ⟨N, hN⟩ := exists_rankCollisionIdeal_finite_kernels E x y σ r s
  exact ⟨N, hN.trans (doubleRankCollisionKernel_radical E x y σ N r s).symm⟩

/-- A safe original prime admits a scalar killing every full off-diagonal stage at these orders. -/
theorem exists_doubleRank_exact_denominator (r s : ℕ) (P : PrimeSpectrum R)
    (hP : ¬ rankCollisionIdeal E x y (scalarMorphism σ) ≤ P.asIdeal) :
    ∃ (N : ℕ) (a : R), a ∉ P.asIdeal ∧
      a ∈ doubleRankCollisionKernel E x y σ N r s ∧
      a ∈ rankCollisionIdeal E x y (scalarMorphism σ) := by
  obtain ⟨N, hN⟩ := exists_rankCollisionIdeal_exact_kernel E x y σ r s
  rw [hN, P.isPrime.radical_le_iff] at hP
  obtain ⟨a, ha, haP⟩ := Set.not_subset.mp hP
  refine ⟨N, a, haP, ha, ?_⟩
  rw [hN]
  exact Ideal.le_radical ha

/-- A common-rank denominator has one power vanishing on every full chart in the rectangle. -/
theorem exists_doubleRank_uniform_power (r s : ℕ) (a : R)
    (ha : a ∈ rankCollisionIdeal E x y (scalarMorphism σ)) :
    ∃ N k : ℕ, ∀ n m : Fin (N + 1), n.val ≠ m.val →
      (doubleRankMap E x y n.val m.val r s).appTop (σ (a ^ k)) = 0 := by
  obtain ⟨N, hN⟩ := exists_rankCollisionIdeal_exact_kernel E x y σ r s
  rw [hN] at ha
  obtain ⟨k, hk⟩ := ha
  exact ⟨N, k, (mem_doubleRankCollisionKernel E x y σ N r s _).mp hk⟩

end FLT.Mazur.RelativeOrderedTuples
