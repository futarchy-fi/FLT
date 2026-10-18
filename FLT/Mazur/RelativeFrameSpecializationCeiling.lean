/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameRankJumpValuations

/-!
# The least rank bound near an unchanged original point

The ranks of all original generizations have a finite attained maximum. Its
value is the least open rank bound at the center. A generization attaining it
lies on a genuine open rank stratum, including when the center itself lies
on the residual closed locus.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  [QuasiCompact E.hom] [NoetherianSpace S]

/-- The full original ranks over all generizations are uniformly bounded. -/
theorem exists_generization_rank_bound (x : S) :
    ∃ N : ℕ, ∀ (y : S) (m : ℕ), y ⤳ x → y ∈ rankImageOpen E m → m ≤ N := by
  obtain ⟨N, hN⟩ := exists_uniform_rank_bound E
  exact ⟨N, fun y m _ hy ↦ hN y m hy⟩

/-- The least bound on original frame ranks at every generization of a fixed original point. -/
def specializationRankCeiling (x : S) : ℕ := by
  classical
  exact Nat.find (exists_generization_rank_bound E x)

/-- The constructed ceiling bounds every actual original generization frame. -/
theorem specializationRankCeiling_spec (x y : S) (m : ℕ) (hyx : y ⤳ x)
    (hy : y ∈ rankImageOpen E m) : m ≤ specializationRankCeiling E x := by
  classical
  exact Nat.find_spec (exists_generization_rank_bound E x) y m hyx hy

/-- The ceiling is the least bound, rather than a possibly unattained uniform overestimate. -/
theorem specializationRankCeiling_minimal (x : S) (N : ℕ)
    (hN : ∀ (y : S) (m : ℕ), y ⤳ x → y ∈ rankImageOpen E m → m ≤ N) :
    specializationRankCeiling E x ≤ N := by
  classical
  exact Nat.find_min' _ hN

/-- Original open rank exclusion has an exact numerical criterion at every point. -/
theorem mem_rankBound_iff_specializationRankCeiling (x : S) (n : ℕ) :
    x ∈ rankBoundOpen E n ↔ specializationRankCeiling E x ≤ n := by
  rw [mem_rankBound_iff_no_specializing_frame]
  constructor
  · intro h
    apply specializationRankCeiling_minimal E x n
    intro y m hyx hym
    by_contra hm
    obtain ⟨z, hz⟩ := rankImageOpen_antitone E (Nat.lt_of_not_ge hm) hym
    exact h z (hz ▸ hyx)
  · intro hn y hy
    exact Nat.not_succ_le_self n
      ((specializationRankCeiling_spec E x _ (n + 1) hy ⟨y, rfl⟩).trans hn)

/-- The ceiling cannot increase when moving from the center to one of its generizations. -/
theorem specializationRankCeiling_le_of_specializes (x y : S) (hyx : y ⤳ x) :
    specializationRankCeiling E y ≤ specializationRankCeiling E x := by
  apply specializationRankCeiling_minimal E y
  intro z m hzy hz
  exact specializationRankCeiling_spec E x z m (hzy.trans hyx) hz

/-- Some actual generization attains the ceiling and lies in that open exact rank stratum. -/
theorem specializationRankCeiling_attained (x : S) :
    ∃ y : S, y ⤳ x ∧ y ∈ rankStratumOpen E (specializationRankCeiling E x) := by
  classical
  let N := specializationRankCeiling E x
  have hP : ∃ y : S, y ⤳ x ∧ y ∈ rankImageOpen E N := by
    by_cases hzero : N = 0
    · obtain ⟨m, hm⟩ := exists_point_rank E x
      exact ⟨x, specializes_rfl, (hm N).mpr (by omega)⟩
    · by_contra h
      have hb : N ≤ N - 1 := by
        apply specializationRankCeiling_minimal E x (N - 1)
        intro y m hyx hym
        have hm : m < N := by
          by_contra hm
          exact h ⟨y, hyx, rankImageOpen_antitone E (Nat.le_of_not_gt hm) hym⟩
        omega
      omega
  obtain ⟨y, hyx, hy⟩ := hP
  refine ⟨y, hyx, hy, ?_⟩
  exact (mem_rankBound_iff_specializationRankCeiling E y N).mpr
    (specializationRankCeiling_le_of_specializes E x y hyx)

end FLT.Mazur.RelativeOrderedTuples
