/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.TateCurve.Abscissa
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.Sequences

/-!
# Inverting the symmetric interior coordinate

The sum of paired coordinate terms is an isometry of the compact open unit
disc into itself. Compactness makes this isometry surjective. For an abscissa
inside the unit disc, this recovers the symmetric parameter `u + q/u`.
-/

@[expose] public section

open ValuativeRel Filter
open scoped Topology

namespace TateCurve

/-- An isometry from a compact metric space to itself is surjective. -/
private theorem surjective_isometry_of_compact {M : Type*} [MetricSpace M] [CompactSpace M]
    {f : M → M} (hf : Isometry f) : Function.Surjective f := by
  have hc : IsClosed (Set.range f) := (isCompact_range hf.continuous).isClosed
  intro x
  apply hc.closure_eq ▸ (show x ∈ closure (Set.range f) from ?_)
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨y, φ, hφ, ht⟩ := CompactSpace.tendsto_subseq (fun n : ℕ ↦ f^[n] x)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp ht.cauchySeq ε hε
  have hdist := hN N le_rfl (N + 1) (by omega)
  have hlt : φ N < φ (N + 1) := hφ (by omega)
  let d := φ (N + 1) - φ N
  have hd : 0 < d := Nat.sub_pos_of_lt hlt
  have he : φ N + d = φ (N + 1) := Nat.add_sub_of_le hlt.le
  have heq : dist x (f^[d] x) = dist (f^[φ N] x) (f^[φ (N + 1)] x) := by
    rw [← he, Function.iterate_add_apply]
    have hi (n : ℕ) (a b : M) : dist (f^[n] a) (f^[n] b) = dist a b := by
      induction n with
      | zero => rfl
      | succ n ih => simpa only [Function.iterate_succ_apply', hf.dist_eq] using ih
    exact (hi (φ N) x (f^[d] x)).symm
  refine ⟨f^[d] x, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
    rw [hm, Function.iterate_succ_apply']
    exact Set.mem_range_self _
  · simpa only [heq, Function.comp_apply] using hdist

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Every element of the open unit disc is the sum of paired coordinates at a unique parameter. -/
theorem existsUnique_tsum_xPair_eq {q a x : K}
    (hq : valuation K q < 1) (ha : valuation K a < 1) (hx : valuation K x < 1) :
    ∃! t : {t : K // valuation K t < 1},
      (∑' n : ℕ, xPair (q ^ (2 * n) * a) (q ^ n * (t : K))) = x := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  let : (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let D := {t : K // valuation K t < 1}
  have hc : IsCompact {t : K | valuation K t < 1} := by
    apply (IsNonarchimedeanLocalField.isCompact_closedBall (K := K) 1).of_isClosed_subset
    · simpa only [(valuation K).restrict_lt_one_iff] using
        (valuation K).isClosed_ball 1
    · intro t ht
      change valuation K t ≤ 1
      exact le_of_lt ht
  let : CompactSpace D := isCompact_iff_compactSpace.mp hc
  let F : D → D := fun t ↦ ⟨∑' n : ℕ, xPair (q ^ (2 * n) * a) (q ^ n * (t : K)),
    (valuation_tsum_xPair_le hq ha t.2).trans_lt (max_lt t.2 ha)⟩
  open scoped Valued in
  have hF : Function.Bijective F := by
    have hi : Isometry F := by
      apply Isometry.of_dist_eq
      intro s t
      change ‖(F s : K) - (F t : K)‖ = ‖(s : K) - (t : K)‖
      apply le_antisymm
      · rw [Valued.toNormedField.norm_le_iff]
        exact (valuation_tsum_xPair_sub hq ha s.2 t.2).le
      · rw [Valued.toNormedField.norm_le_iff]
        exact (valuation_tsum_xPair_sub hq ha s.2 t.2).ge
    exact ⟨hi.injective, surjective_isometry_of_compact hi⟩
  obtain ⟨t, ht⟩ := hF.2 ⟨x, hx⟩
  refine ⟨t, congrArg Subtype.val ht, ?_⟩
  intro s hs
  apply hF.1
  exact (Subtype.ext hs).trans ht.symm

/-- An interior abscissa determines a unique symmetric parameter. Recovering `u` then
requires solving `u² - tu + q = 0`. -/
theorem existsUnique_interior_symmetric_parameter {q x : K}
    (hq : valuation K q < 1) (hx : valuation K x < 1) :
    ∃! t : {t : K // valuation K t < 1},
      (∑' n : ℕ, xPair (q ^ (2 * n) * q) (q ^ n * (t : K))) -
        2 * tateCorrection q = x := by
  have htarget : valuation K (x + 2 * tateCorrection q) < 1 := by
    apply (Valuation.map_add _ _ _).trans_lt
    apply max_lt hx
    rw [map_mul]
    exact ((mul_le_of_le_one_left' (valuation_natCast_le_one (R := K) 2)).trans
      (valuation_tateCorrection_le hq)).trans_lt hq
  simpa only [sub_eq_iff_eq_add] using existsUnique_tsum_xPair_eq hq hq htarget

end TateCurve
