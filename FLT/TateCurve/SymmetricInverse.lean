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

/-- The bounded tail of the boundary abscissa after setting `z = u + u⁻¹ - 2`. -/
noncomputable def boundaryTail (q z : K) : K :=
  (∑' n : ℕ, xPair (q ^ (2 * n) * q ^ 2) (q ^ n * (q * (z + 2)))) -
    2 * tateCorrection q

/-- The symmetric boundary tail stays strictly inside the unit disc. -/
theorem valuation_boundaryTail_lt_one {q z : K}
    (hq : valuation K q < 1) (hz : valuation K z ≤ 1) :
    valuation K (boundaryTail q z) < 1 := by
  have hs : valuation K (z + 2) ≤ 1 := (Valuation.map_add _ _ _).trans
    (max_le hz (valuation_natCast_le_one (R := K) 2))
  have hqs : valuation K (q * (z + 2)) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_right' hs).trans_lt hq
  have hq2 : valuation K (q ^ 2) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le hq (by decide)
  apply (Valuation.map_sub _ _ _).trans_lt
  apply max_lt ((valuation_tsum_xPair_le hq hq2 hqs).trans_lt (max_lt hqs hq2))
  rw [map_mul]
  exact ((mul_le_of_le_one_left' (valuation_natCast_le_one (R := K) 2)).trans
    (valuation_tateCorrection_le hq)).trans_lt hq

/-- Differences of the boundary tail are smaller by the factor `|q|`. -/
theorem valuation_boundaryTail_sub {q z w : K} (hq : valuation K q < 1)
    (hz : valuation K z ≤ 1) (hw : valuation K w ≤ 1) :
    valuation K (boundaryTail q z - boundaryTail q w) =
      valuation K q * valuation K (z - w) := by
  have hsmall {t : K} (ht : valuation K t ≤ 1) : valuation K (q * (t + 2)) < 1 := by
    rw [map_mul]
    apply (mul_le_of_le_one_right' _).trans_lt hq
    exact (Valuation.map_add _ _ _).trans (max_le ht (valuation_natCast_le_one (R := K) 2))
  have hq2 : valuation K (q ^ 2) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le hq (by decide)
  rw [boundaryTail, boundaryTail, sub_sub_sub_cancel_right,
    valuation_tsum_xPair_sub hq hq2 (hsmall hz) (hsmall hw), ← mul_sub,
    add_sub_add_right_eq_sub, map_mul]

/-- The reciprocal boundary abscissa extends across `z = 0`. -/
noncomputable def boundaryReciprocal (q z : K) : K := z / (1 + z * boundaryTail q z)

/-- The denominator of the reciprocal boundary coordinate has valuation one. -/
theorem valuation_boundaryReciprocal_denominator {q z : K}
    (hq : valuation K q < 1) (hz : valuation K z ≤ 1) :
    valuation K (1 + z * boundaryTail q z) = 1 := by
  apply (valuation K).map_one_add_of_lt
  rw [map_mul]
  exact (mul_le_of_le_one_left' hz).trans_lt (valuation_boundaryTail_lt_one hq hz)

/-- The reciprocal boundary coordinate preserves the valuation of its argument. -/
theorem valuation_boundaryReciprocal {q z : K}
    (hq : valuation K q < 1) (hz : valuation K z ≤ 1) :
    valuation K (boundaryReciprocal q z) = valuation K z := by
  rw [boundaryReciprocal, map_div₀, valuation_boundaryReciprocal_denominator hq hz, div_one]

/-- The reciprocal boundary coordinate preserves distances on the closed unit ball. -/
theorem valuation_boundaryReciprocal_sub {q z w : K} (hq : valuation K q < 1)
    (hz : valuation K z ≤ 1) (hw : valuation K w ≤ 1) :
    valuation K (boundaryReciprocal q z - boundaryReciprocal q w) =
      valuation K (z - w) := by
  by_cases heq : z = w
  · simp [heq]
  have hden {t : K} (ht : valuation K t ≤ 1) : 1 + t * boundaryTail q t ≠ 0 := by
    intro h
    have he := valuation_boundaryReciprocal_denominator hq ht
    simp [h] at he
  have he : boundaryReciprocal q z - boundaryReciprocal q w =
      ((z - w) + z * w * (boundaryTail q w - boundaryTail q z)) /
        ((1 + z * boundaryTail q z) * (1 + w * boundaryTail q w)) := by
    unfold boundaryReciprocal
    field_simp [hden hz, hden hw]
    ring
  have hsmall : valuation K (z * w * (boundaryTail q w - boundaryTail q z)) <
      valuation K (z - w) := by
    rw [map_mul, map_mul, valuation_boundaryTail_sub hq hw hz,
      (valuation K).map_sub_swap w z]
    apply (mul_le_of_le_one_left' ((mul_le_of_le_one_right' hw).trans hz)).trans_lt
    simpa only [one_mul] using mul_lt_mul_of_pos_right hq
      (zero_lt_iff.mpr ((valuation K).ne_zero_iff.mpr (sub_ne_zero.mpr heq)))
  rw [he, map_div₀, map_mul, valuation_boundaryReciprocal_denominator hq hz,
    valuation_boundaryReciprocal_denominator hq hw, one_mul, div_one,
    (valuation K).map_add_eq_of_lt_left hsmall]

/-- Every element of the closed unit ball has a unique reciprocal boundary parameter. -/
theorem existsUnique_boundaryReciprocal_eq {q x : K}
    (hq : valuation K q < 1) (hx : valuation K x ≤ 1) :
    ∃! z : {z : K // valuation K z ≤ 1}, boundaryReciprocal q z = x := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  let : (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let D := {z : K // valuation K z ≤ 1}
  let : CompactSpace D := isCompact_iff_compactSpace.mp
    (IsNonarchimedeanLocalField.isCompact_closedBall K 1)
  let F : D → D := fun z ↦ ⟨boundaryReciprocal q z,
    (valuation_boundaryReciprocal hq z.2).le.trans z.2⟩
  open scoped Valued in
  have hF : Function.Bijective F := by
    have hi : Isometry F := by
      apply Isometry.of_dist_eq
      intro z w
      change ‖(F z : K) - (F w : K)‖ = ‖(z : K) - (w : K)‖
      apply le_antisymm
      · rw [Valued.toNormedField.norm_le_iff]
        exact (valuation_boundaryReciprocal_sub hq z.2 w.2).le
      · rw [Valued.toNormedField.norm_le_iff]
        exact (valuation_boundaryReciprocal_sub hq z.2 w.2).ge
    exact ⟨hi.injective, surjective_isometry_of_compact hi⟩
  obtain ⟨z, hz⟩ := hF.2 ⟨x, hx⟩
  refine ⟨z, congrArg Subtype.val hz, ?_⟩
  intro w hw
  apply hF.1
  exact (Subtype.ext hw).trans hz.symm

/-- An abscissa of valuation at least one has a nonzero symmetric boundary parameter. -/
theorem exists_boundary_symmetric_parameter {q x : K}
    (hq : valuation K q < 1) (hx : 1 ≤ valuation K x) :
    ∃ z : K, z ≠ 0 ∧ valuation K z ≤ 1 ∧ 1 / z + boundaryTail q z = x := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hxi : valuation K x⁻¹ ≤ 1 := by
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ hx
  obtain ⟨z, hz, -⟩ := existsUnique_boundaryReciprocal_eq hq hxi
  have hz0 : (z : K) ≠ 0 := by
    intro h
    have he : (0 : K) = x⁻¹ := by simpa [boundaryReciprocal, h] using hz
    exact inv_ne_zero hx0 he.symm
  refine ⟨z, hz0, z.2, ?_⟩
  have hd : 1 + (z : K) * boundaryTail q z ≠ 0 := by
    intro h
    have he := valuation_boundaryReciprocal_denominator hq z.2
    simp [h] at he
  change (z : K) / (1 + (z : K) * boundaryTail q z) = x⁻¹ at hz
  field_simp at hz ⊢
  linear_combination -hz

end TateCurve
