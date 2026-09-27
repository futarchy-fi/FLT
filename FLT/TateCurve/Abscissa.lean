/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.TateCurve.LocalField

/-!
# Separating Tate abscissae

Pairing opposite tails expresses the abscissa through a symmetric parameter.
The resulting rational function preserves distances on the open unit disc.
-/

@[expose] public section

open ValuativeRel

namespace TateCurve

section Algebra

variable {K : Type*} [Field K]

/-- The sum of two rational coordinate terms, in their sum and product. -/
def xPair (a t : K) : K := ((1 + a) * t - 4 * a) / (1 + a - t) ^ 2

/-- Pairing two rational coordinate terms removes their individual parameters. -/
theorem xTerm_add_xTerm {u v : K} (hu : 1 - u ≠ 0) (hv : 1 - v ≠ 0) :
    xTerm u + xTerm v = xPair (u * v) (u + v) := by
  have hd : 1 + u * v - (u + v) ≠ 0 := by
    convert mul_ne_zero hu hv using 1
    ring
  unfold xTerm xPair
  field_simp
  ring

/-- The divided difference of the paired rational coordinate. -/
def xPairSlope (a s t : K) : K :=
  ((1 + a) ^ 3 - 8 * a * (1 + a) + 4 * a * (s + t) - (1 + a) * s * t) /
    ((1 + a - s) ^ 2 * (1 + a - t) ^ 2)

/-- The paired rational coordinate has an explicit divided difference in every characteristic. -/
theorem xPair_sub_xPair {a s t : K}
    (hs : 1 + a - s ≠ 0) (ht : 1 + a - t ≠ 0) :
    xPair a s - xPair a t = (s - t) * xPairSlope a s t := by
  unfold xPair xPairSlope
  field_simp
  ring

end Algebra

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A convergent sum stays inside any closed valuation ball containing all its terms. -/
theorem valuation_tsum_le {ι : Type*} {f : ι → K} (hf : Summable f)
    {r : ValueGroupWithZero K} (hr : ∀ i, valuation K (f i) ≤ r) :
    valuation K (∑' i, f i) ≤ r := by
  by_contra h
  have hlt : r < valuation K (∑' i, f i) := lt_of_not_ge h
  have hs := hf.hasSum
  simp only [HasSum, SummationFilter.unconditional_filter,
    (IsValuativeTopology.hasBasis_nhds (∑' i, f i)).tendsto_right_iff] at hs
  obtain ⟨s, hs⟩ := (hs (Units.mk0 _ (ne_of_gt (zero_le.trans_lt hlt))) trivial).exists
  have hp : valuation K (∑ i ∈ s, f i) ≤ r := Valuation.map_sum_le _ fun i _ ↦ hr i
  have he : (∑' i, f i) = (∑ i ∈ s, f i) - ((∑ i ∈ s, f i) - ∑' i, f i) := by ring
  exact (lt_irrefl (valuation K (∑' i, f i)))
    (calc valuation K (∑' i, f i)
      _ = valuation K ((∑ i ∈ s, f i) - ((∑ i ∈ s, f i) - ∑' i, f i)) := congrArg _ he
      _ ≤ max _ _ := Valuation.map_sub _ _ _
      _ < _ := max_lt (hp.trans_lt hlt) hs)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The denominator of a paired coordinate is a valuation unit on the open unit disc. -/
theorem valuation_xPair_denominator {a t : K}
    (ha : valuation K a < 1) (ht : valuation K t < 1) :
    valuation K (1 + a - t) = 1 := by
  have h : valuation K (a - t) < 1 := (Valuation.map_sub _ _ _).trans_lt (max_lt ha ht)
  simpa only [add_sub_assoc] using (valuation K).map_one_add_of_lt h

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The divided difference of a paired coordinate is a valuation unit on the open unit disc. -/
theorem valuation_xPairSlope {a s t : K}
    (ha : valuation K a < 1) (hs : valuation K s < 1) (ht : valuation K t < 1) :
    valuation K (xPairSlope a s t) = 1 := by
  have ha1 : valuation K (1 + a) = 1 := (valuation K).map_one_add_of_lt ha
  have hst : valuation K (s + t) < 1 := (Valuation.map_add _ _ _).trans_lt (max_lt hs ht)
  have h8 : valuation K (8 * a * (1 + a)) < 1 := by
    rw [map_mul, map_mul, ha1, mul_one]
    exact (mul_le_of_le_one_left' (valuation_natCast_le_one (R := K) 8)).trans_lt ha
  have h4 : valuation K (4 * a * (s + t)) < 1 := by
    rw [map_mul, map_mul]
    exact (mul_le_of_le_one_right' hst.le).trans_lt
      ((mul_le_of_le_one_left' (valuation_natCast_le_one (R := K) 4)).trans_lt ha)
  have hlast : valuation K ((1 + a) * s * t) < 1 := by
    rw [map_mul, map_mul, ha1, one_mul]
    exact (mul_le_of_le_one_right' ht.le).trans_lt hs
  have hsmall : valuation K (-8 * a * (1 + a) + 4 * a * (s + t) -
      (1 + a) * s * t) < 1 := by
    apply (Valuation.map_sub _ _ _).trans_lt
    apply max_lt _ hlast
    apply (Valuation.map_add _ _ _).trans_lt
    exact max_lt (by simpa only [neg_mul, Valuation.map_neg] using h8) h4
  have hn : valuation K ((1 + a) ^ 3 - 8 * a * (1 + a) + 4 * a * (s + t) -
      (1 + a) * s * t) = 1 := by
    have he : (1 + a) ^ 3 - 8 * a * (1 + a) + 4 * a * (s + t) - (1 + a) * s * t =
        (1 + a) ^ 3 + (-8 * a * (1 + a) + 4 * a * (s + t) - (1 + a) * s * t) := by ring
    rw [he, (valuation K).map_add_eq_of_lt_left (by simpa [map_pow, ha1] using hsmall),
      map_pow, ha1, one_pow]
  rw [xPairSlope, map_div₀, hn, map_mul, map_pow, map_pow,
    valuation_xPair_denominator ha hs, valuation_xPair_denominator ha ht]
  simp

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Pairing preserves the valuation of a difference in its symmetric parameter. -/
theorem valuation_xPair_sub {a s t : K}
    (ha : valuation K a < 1) (hs : valuation K s < 1) (ht : valuation K t < 1) :
    valuation K (xPair a s - xPair a t) = valuation K (s - t) := by
  have hn {r : K} (hr : valuation K r < 1) : 1 + a - r ≠ 0 := by
    intro h
    have := valuation_xPair_denominator ha hr
    simp [h] at this
  rw [xPair_sub_xPair (hn hs) (hn ht), map_mul, valuation_xPairSlope ha hs ht, mul_one]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The size of a paired coordinate is bounded by its two symmetric parameters. -/
theorem valuation_xPair_le {a t : K}
    (ha : valuation K a < 1) (ht : valuation K t < 1) :
    valuation K (xPair a t) ≤ max (valuation K t) (valuation K a) := by
  rw [xPair, map_div₀, map_pow, valuation_xPair_denominator ha ht, one_pow, div_one]
  apply (Valuation.map_sub _ _ _).trans
  apply max_le_max
  · rw [map_mul, (valuation K).map_one_add_of_lt ha, one_mul]
  · rw [map_mul]
    exact mul_le_of_le_one_left' (valuation_natCast_le_one (R := K) 4)

/-- The paired rational series converges on the open unit disc. -/
theorem summable_xPair {q a t : K} (hq : valuation K q < 1)
    (ha : valuation K a < 1) (ht : valuation K t < 1) :
    Summable (fun n : ℕ ↦ xPair (q ^ (2 * n) * a) (q ^ n * t)) := by
  apply summable_of_valuation_le_pow hq (fun n ↦ n) (fun N ↦ Set.finite_Iio N)
  intro n
  have hp (m : ℕ) : valuation K (q ^ m) ≤ 1 := by
    rw [map_pow]
    exact pow_le_one₀ zero_le hq.le
  have ha' : valuation K (q ^ (2 * n) * a) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_left' (hp _)).trans_lt ha
  have ht' : valuation K (q ^ n * t) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_left' (hp _)).trans_lt ht
  apply (valuation_xPair_le ha' ht').trans
  apply max_le
  · rw [map_mul, map_pow]
    exact mul_le_of_le_one_right' ht.le
  · rw [map_mul, map_pow]
    exact (mul_le_of_le_one_right' ha.le).trans
      (pow_le_pow_right_of_le_one' hq.le (by omega))

/-- Summing paired coordinates preserves distances in the symmetric parameter. -/
theorem valuation_tsum_xPair_sub {q a s t : K} (hq : valuation K q < 1)
    (ha : valuation K a < 1) (hs : valuation K s < 1) (ht : valuation K t < 1) :
    valuation K ((∑' n : ℕ, xPair (q ^ (2 * n) * a) (q ^ n * s)) -
      ∑' n : ℕ, xPair (q ^ (2 * n) * a) (q ^ n * t)) = valuation K (s - t) := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  by_cases heq : s = t
  · simp [heq]
  let f (n : ℕ) := xPair (q ^ (2 * n) * a) (q ^ n * s) -
    xPair (q ^ (2 * n) * a) (q ^ n * t)
  have hf : Summable f := (summable_xPair hq ha hs).sub (summable_xPair hq ha ht)
  have hval (n : ℕ) : valuation K (f n) = valuation K q ^ n * valuation K (s - t) := by
    have hp (m : ℕ) : valuation K (q ^ m) ≤ 1 := by
      rw [map_pow]
      exact pow_le_one₀ zero_le hq.le
    have hmul {r : K} (hr : valuation K r < 1) (m : ℕ) :
        valuation K (q ^ m * r) < 1 := by
      rw [map_mul]
      exact (mul_le_of_le_one_left' (hp m)).trans_lt hr
    dsimp only [f]
    rw [valuation_xPair_sub (hmul ha _) (hmul hs _) (hmul ht _),
      ← mul_sub, map_mul, map_pow]
  rw [← (summable_xPair hq ha hs).tsum_sub (summable_xPair hq ha ht)]
  change valuation K (∑' n, f n) = _
  rw [hf.tsum_eq_zero_add]
  have htail : valuation K (∑' n : ℕ, f (n + 1)) ≤
      valuation K q * valuation K (s - t) := by
    apply valuation_tsum_le ((summable_nat_add_iff (f := f) 1).mpr hf)
    intro n
    rw [hval]
    exact mul_le_mul_left
      (by simpa only [pow_one] using pow_le_pow_right_of_le_one' hq.le (Nat.succ_pos n)) _
  have hsmall : valuation K (∑' n : ℕ, f (n + 1)) < valuation K (f 0) := by
    rw [hval, pow_zero, one_mul]
    apply htail.trans_lt
    simpa only [one_mul] using mul_lt_mul_of_pos_right hq
      (zero_lt_iff.mpr ((valuation K).ne_zero_iff.mpr (sub_ne_zero.mpr heq)))
  rw [(valuation K).map_add_eq_of_lt_left hsmall, hval, pow_zero, one_mul]

/-- Pair the nonnegative and negative tails of the Tate abscissa. -/
theorem tateX_eq_tsum_xPair {q u : K} (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq : valuation K q < 1) (hu : valuation K u < 1)
    (hqu : valuation K (q / u) < 1) :
    tateX u q = (∑' n : ℕ, xPair (q ^ (2 * n) * q) (q ^ n * (u + q / u))) -
      2 * tateCorrection q := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  have hf := summable_tate_x_of_valuation_lt_one hq0 hu0 hq
  have hp : Summable (fun n : ℕ ↦ xTerm (q ^ (n : ℤ) * u)) :=
    hf.comp_injective (Nat.cast_injective : Function.Injective (fun n : ℕ ↦ (n : ℤ)))
  have hn : Summable (fun n : ℕ ↦ xTerm (q ^ (-((n : ℤ) + 1)) * u)) :=
    hf.comp_injective (i := fun n : ℕ ↦ -((n : ℤ) + 1)) (by intro a b h; dsimp at h; omega)
  rw [tateX, tsum_of_nat_of_neg_add_one (f := fun n : ℤ ↦ xTerm (q ^ n * u)) hp hn,
    ← hp.tsum_add hn]
  congr 1
  apply tsum_congr
  intro n
  have hneg : q ^ (-((n : ℤ) + 1)) * u = (q ^ n * (q / u))⁻¹ := by
    simp [div_eq_mul_inv, zpow_add₀ hq0, zpow_neg, mul_assoc, mul_comm]
  rw [hneg, xTerm_inv (mul_ne_zero (pow_ne_zero _ hq0) (div_ne_zero hq0 hu0)), zpow_natCast]
  have hsmall {r : K} (hr : valuation K r < 1) : 1 - q ^ n * r ≠ 0 := by
    have hv : valuation K (q ^ n * r) < 1 := by
      rw [map_mul, map_pow]
      exact (mul_le_of_le_one_left' (pow_le_one₀ zero_le hq.le)).trans_lt hr
    intro h
    have he := (valuation K).map_one_sub_of_lt hv
    simp [h] at he
  rw [xTerm_add_xTerm (hsmall hu) (hsmall hqu)]
  congr 1
  · field_simp
    ring
  · ring

/-- Inside the fundamental annulus, the abscissa preserves distances in `u + q/u`. -/
theorem valuation_tateX_sub_of_open_annulus {q u v : K}
    (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hq : valuation K q < 1)
    (hu : valuation K u < 1) (hqu : valuation K (q / u) < 1)
    (hv : valuation K v < 1) (hqv : valuation K (q / v) < 1) :
    valuation K (tateX u q - tateX v q) = valuation K ((u + q / u) - (v + q / v)) := by
  rw [tateX_eq_tsum_xPair hq0 hu0 hq hu hqu, tateX_eq_tsum_xPair hq0 hv0 hq hv hqv,
    sub_sub_sub_cancel_right]
  exact valuation_tsum_xPair_sub hq hq
    ((Valuation.map_add _ _ _).trans_lt (max_lt hu hqu))
    ((Valuation.map_add _ _ _).trans_lt (max_lt hv hqv))

/-- Two interior representatives have equal abscissae exactly when equal or inverse modulo `q`. -/
theorem tateX_eq_iff_of_open_annulus {q u v : K}
    (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hq : valuation K q < 1)
    (hu : valuation K u < 1) (hqu : valuation K (q / u) < 1)
    (hv : valuation K v < 1) (hqv : valuation K (q / v) < 1) :
    tateX u q = tateX v q ↔ u = v ∨ u * v = q := by
  rw [← sub_eq_zero, ← (valuation K).zero_iff,
    valuation_tateX_sub_of_open_annulus hq0 hu0 hv0 hq hu hqu hv hqv,
    (valuation K).zero_iff]
  have he : (u + q / u) - (v + q / v) = (u - v) * (u * v - q) / (u * v) := by
    field_simp
    ring
  rw [he, div_eq_zero_iff, or_iff_left (mul_ne_zero hu0 hv0), mul_eq_zero,
    sub_eq_zero, sub_eq_zero]

/-- Uniform bound on a sum of paired coordinates inside the open unit disc. -/
theorem valuation_tsum_xPair_le {q a t : K} (hq : valuation K q < 1)
    (ha : valuation K a < 1) (ht : valuation K t < 1) :
    valuation K (∑' n : ℕ, xPair (q ^ (2 * n) * a) (q ^ n * t)) ≤
      max (valuation K t) (valuation K a) := by
  apply valuation_tsum_le (summable_xPair hq ha ht)
  intro n
  have hm {r : K} (m : ℕ) : valuation K (q ^ m * r) ≤ valuation K r := by
    rw [map_mul, map_pow]
    exact mul_le_of_le_one_left' (pow_le_one₀ zero_le hq.le)
  exact (valuation_xPair_le ((hm _).trans_lt ha) ((hm _).trans_lt ht)).trans
    (max_le_max (hm _) (hm _))

/-- The correction series is strictly inside the unit disc. -/
theorem valuation_tateCorrection_le {q : K} (hq : valuation K q < 1) :
    valuation K (tateCorrection q) ≤ valuation K q := by
  rw [tateCorrection_eq_evalInt hq]
  simpa only [pow_one] using valuation_evalInt_le_pow q hq (F := sInt 1) (M := 1)
    (by
      intro m hm
      have hm0 : m = 0 := by omega
      subst m
      simp [sInt])

/-- Interior representatives have abscissae strictly inside the unit disc. -/
theorem valuation_tateX_lt_one_of_open_annulus {q u : K}
    (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq : valuation K q < 1)
    (hu : valuation K u < 1) (hqu : valuation K (q / u) < 1) :
    valuation K (tateX u q) < 1 := by
  have ht : valuation K (u + q / u) < 1 :=
    (Valuation.map_add _ _ _).trans_lt (max_lt hu hqu)
  rw [tateX_eq_tsum_xPair hq0 hu0 hq hu hqu]
  apply (Valuation.map_sub _ _ _).trans_lt
  apply max_lt ((valuation_tsum_xPair_le hq hq ht).trans_lt (max_lt ht hq))
  rw [map_mul]
  exact ((mul_le_of_le_one_left' (valuation_natCast_le_one (R := K) 2)).trans
    (valuation_tateCorrection_le hq)).trans_lt hq

/-- Pair both nonzero tails while retaining the pole term on the unit circle. -/
theorem tateX_eq_xTerm_add_tsum_xPair {q u : K} (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq : valuation K q < 1) (hu : valuation K u = 1) :
    tateX u q = xTerm u +
      (∑' n : ℕ, xPair (q ^ (2 * n) * q ^ 2) (q ^ n * (q * (u + u⁻¹)))) -
        2 * tateCorrection q := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  have hf := summable_tate_x_of_valuation_lt_one hq0 hu0 hq
  have hp : Summable (fun n : ℕ ↦ xTerm (q ^ (n : ℤ) * u)) :=
    hf.comp_injective (Nat.cast_injective : Function.Injective (fun n : ℕ ↦ (n : ℤ)))
  have hn : Summable (fun n : ℕ ↦ xTerm (q ^ (-((n : ℤ) + 1)) * u)) :=
    hf.comp_injective (i := fun n : ℕ ↦ -((n : ℤ) + 1)) (by intro a b h; dsimp at h; omega)
  rw [tateX, tsum_of_nat_of_neg_add_one (f := fun n : ℤ ↦ xTerm (q ^ n * u)) hp hn,
    hp.tsum_eq_zero_add, add_assoc,
    ← ((summable_nat_add_iff 1).mpr hp).tsum_add hn]
  simp only [Nat.cast_zero, zpow_zero, one_mul]
  congr 2
  apply tsum_congr
  intro n
  have hneg : q ^ (-((n : ℤ) + 1)) * u = (q ^ (n + 1) * u⁻¹)⁻¹ := by
    simp only [zpow_neg, zpow_add₀ hq0, zpow_natCast, zpow_one, pow_succ,
      mul_inv_rev, inv_inv]
    ring
  rw [hneg, xTerm_inv (mul_ne_zero (pow_ne_zero _ hq0) (inv_ne_zero hu0))]
  simp only [zpow_natCast]
  have hsmall {r : K} (hr : valuation K r = 1) : 1 - q ^ (n + 1) * r ≠ 0 := by
    have hv : valuation K (q ^ (n + 1) * r) < 1 := by
      rw [map_mul, map_pow, hr, mul_one]
      exact pow_lt_one₀ zero_le hq (Nat.succ_ne_zero n)
    intro h
    have he := (valuation K).map_one_sub_of_lt hv
    simp [h] at he
  rw [xTerm_add_xTerm (hsmall hu) (hsmall (by rw [map_inv₀, hu, inv_one]))]
  congr 1
  · rw [mul_mul_mul_comm, mul_inv_cancel₀ hu0, mul_one]
    ring
  · ring

/-- On the unit circle the only equal abscissae come from equal or inverse arguments. -/
theorem tateX_eq_iff_of_valuation_eq_one {q u v : K}
    (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (hq : valuation K q < 1) (hu : valuation K u = 1) (hv : valuation K v = 1) :
    tateX u q = tateX v q ↔ u = v ∨ u * v = 1 := by
  let S (t : K) := ∑' n : ℕ, xPair (q ^ (2 * n) * q ^ 2) (q ^ n * (q * t))
  have hsum {w : K} (hw0 : w ≠ 0) (hw : valuation K w = 1) :
      tateX w q = xTerm w + S (w + w⁻¹) - 2 * tateCorrection q :=
    tateX_eq_xTerm_add_tsum_xPair hq0 hw0 hq hw
  have ht {w : K} (hw : valuation K w = 1) : valuation K (w + w⁻¹) ≤ 1 := by
    apply (Valuation.map_add _ _ _).trans
    simp [hw, map_inv₀]
  have hqt {w : K} (hw : valuation K w = 1) : valuation K (q * (w + w⁻¹)) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_right' (ht hw)).trans_lt hq
  have hd : valuation K (S (u + u⁻¹) - S (v + v⁻¹)) =
      valuation K q * valuation K ((u + u⁻¹) - (v + v⁻¹)) := by
    dsimp only [S]
    have hq2 : valuation K (q ^ 2) < 1 := by
      rw [map_pow]
      exact pow_lt_one₀ zero_le hq (by decide)
    rw [valuation_tsum_xPair_sub hq hq2 (hqt hu) (hqt hv), ← mul_sub, map_mul]
  have he : xTerm u - xTerm v =
      (u - v) * (1 - u * v) / ((1 - u) ^ 2 * (1 - v) ^ 2) := by
    unfold xTerm
    field_simp
    ring
  have he' : (u + u⁻¹) - (v + v⁻¹) =
      -(xTerm u - xTerm v) * ((1 - u) ^ 2 * (1 - v) ^ 2) / (u * v) := by
    rw [he]
    field_simp
    ring
  have hle : valuation K ((u + u⁻¹) - (v + v⁻¹)) ≤ valuation K (xTerm u - xTerm v) := by
    rw [he', map_div₀]
    simp only [map_mul, hu, hv, one_mul, div_one, Valuation.map_neg]
    apply mul_le_of_le_one_right'
    rw [map_pow, map_pow]
    exact (mul_le_of_le_one_right'
      (pow_le_one₀ zero_le ((Valuation.map_sub _ _ _).trans (by simp [hv])))).trans
        (pow_le_one₀ zero_le ((Valuation.map_sub _ _ _).trans (by simp [hu])))
  have hden : (1 - u) ^ 2 * (1 - v) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hu1.symm))
      (pow_ne_zero _ (sub_ne_zero.mpr hv1.symm))
  have heq : xTerm u = xTerm v ↔ u = v ∨ u * v = 1 := by
    rw [← sub_eq_zero, he, div_eq_zero_iff, or_iff_left hden, mul_eq_zero,
      sub_eq_zero, sub_eq_zero, eq_comm (a := (1 : K))]
  constructor
  · intro h
    apply heq.mp
    by_contra hn
    have hrelation : xTerm u - xTerm v = -(S (u + u⁻¹) - S (v + v⁻¹)) := by
      rw [hsum hu0 hu, hsum hv0 hv] at h
      linear_combination h
    have hbound : valuation K (xTerm u - xTerm v) ≤
        valuation K q * valuation K (xTerm u - xTerm v) := by
      calc valuation K (xTerm u - xTerm v)
        _ = valuation K (S (u + u⁻¹) - S (v + v⁻¹)) := by
          rw [hrelation, Valuation.map_neg]
        _ = _ := hd
        _ ≤ _ := mul_le_mul_right hle _
    have hstrict : valuation K q * valuation K (xTerm u - xTerm v) <
        valuation K (xTerm u - xTerm v) := by
      simpa only [one_mul] using mul_lt_mul_of_pos_right hq
        (zero_lt_iff.mpr ((valuation K).ne_zero_iff.mpr (sub_ne_zero.mpr hn)))
    exact (lt_irrefl _ (hbound.trans_lt hstrict))
  · rintro (rfl | huv)
    · rfl
    · have hvu : v = u⁻¹ := eq_inv_of_mul_eq_one_right huv
      rw [hvu, tateX_inv hq0 hu0]

/-- On the unit circle, the pole term dominates the two tails and the correction. -/
theorem one_le_valuation_tateX_of_valuation_eq_one {q u : K}
    (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hu1 : u ≠ 1)
    (hq : valuation K q < 1) (hu : valuation K u = 1) :
    1 ≤ valuation K (tateX u q) := by
  have hs : valuation K (u + u⁻¹) ≤ 1 := by
    apply (Valuation.map_add _ _ _).trans
    simp [hu, map_inv₀]
  have hqs : valuation K (q * (u + u⁻¹)) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_right' hs).trans_lt hq
  have hq2 : valuation K (q ^ 2) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le hq (by decide)
  have htail : valuation K ((∑' n : ℕ, xPair (q ^ (2 * n) * q ^ 2)
      (q ^ n * (q * (u + u⁻¹)))) - 2 * tateCorrection q) < 1 := by
    apply (Valuation.map_sub _ _ _).trans_lt
    apply max_lt ((valuation_tsum_xPair_le hq hq2 hqs).trans_lt (max_lt hqs hq2))
    rw [map_mul]
    exact ((mul_le_of_le_one_left' (valuation_natCast_le_one (R := K) 2)).trans
      (valuation_tateCorrection_le hq)).trans_lt hq
  have hmain : 1 ≤ valuation K (xTerm u) := by
    rw [xTerm, map_div₀, map_pow, hu]
    apply (one_le_div₀ (pow_pos (zero_lt_iff.mpr ((valuation K).ne_zero_iff.mpr
      (sub_ne_zero.mpr hu1.symm))) 2)).mpr
    exact pow_le_one₀ zero_le ((Valuation.map_sub _ _ _).trans (by simp [hu]))
  rw [tateX_eq_xTerm_add_tsum_xPair hq0 hu0 hq hu, add_sub_assoc,
    (valuation K).map_add_eq_of_lt_left (htail.trans_le hmain)]
  exact hmain

end TateCurve
