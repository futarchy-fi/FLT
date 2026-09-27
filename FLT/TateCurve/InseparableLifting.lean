/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.TateCurve.SeparableLifting
/-!
# The inseparable symmetric Tate quadratic

In characteristic two, pairing the ordinate series at `u² = q` writes it as
`-u * ordinateCoefficient q + tateCorrection q`. The coefficient has valuation
one. A rational ordinate therefore recovers a rational parameter, completing
the interior quadratic lifting argument.
-/

@[expose] public section

open ValuativeRel
namespace TateCurve
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
/-- The ordinate at a square root of the period is a paired half-series. -/
theorem tateY_of_sq_eq {q u : K} (hq0 : q ≠ 0) (hq : valuation K q < 1)
    (huq : u ^ 2 = q) :
    tateY u q = -(∑' n : ℕ, xTerm (q ^ n * u)) + tateCorrection q := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  have hu0 : u ≠ 0 := fun h ↦ hq0 (huq.symm.trans (by simp [h]))
  have hf := summable_tate_y hq0 hu0 (tendsto_pow_nhds_zero hq)
  have hp : Summable (fun n : ℕ ↦ yTerm (q ^ (n : ℤ) * u)) :=
    hf.comp_injective (Nat.cast_injective : Function.Injective (fun n : ℕ ↦ (n : ℤ)))
  have hn : Summable (fun n : ℕ ↦ yTerm (q ^ (-((n : ℤ) + 1)) * u)) :=
    hf.comp_injective (i := fun n : ℕ ↦ -((n : ℤ) + 1)) (by intro a b h; dsimp at h; omega)
  rw [tateY, tsum_of_nat_of_neg_add_one (f := fun n : ℤ ↦ yTerm (q ^ n * u)) hp hn,
    ← hp.tsum_add hn, ← tsum_neg]
  congr 1
  apply tsum_congr
  intro n
  have he : q ^ (-((n : ℤ) + 1)) * u = (q ^ n * u)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [mul_mul_mul_comm, ← pow_two, huq, ← zpow_natCast,
      ← zpow_add₀ hq0]
    norm_num [hq0]
  rw [he, yTerm_inv_eq (mul_ne_zero (pow_ne_zero _ hq0) hu0), zpow_natCast]
  ring

/-- The coefficient that recovers a ramified quadratic parameter from its ordinate. -/
noncomputable def ordinateCoefficient (q : K) : K :=
  ∑' n : ℕ, q ^ n / (1 - q ^ (2 * n + 1))

/-- The ordinate coefficient series converges on the open unit disc. -/
theorem summable_ordinateCoefficient {q : K} (hq : valuation K q < 1) :
    Summable (fun n : ℕ ↦ q ^ n / (1 - q ^ (2 * n + 1))) := by
  apply summable_of_valuation_le_pow hq (fun n ↦ n) (fun N ↦ Set.finite_Iio N)
  intro n
  have hp : valuation K (q ^ (2 * n + 1)) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le hq (by omega)
  rw [map_div₀, (valuation K).map_one_sub_of_lt hp, div_one, map_pow]

/-- The ordinate coefficient is a unit in the valuation ring. -/
theorem valuation_ordinateCoefficient {q : K} (hq : valuation K q < 1) :
    valuation K (ordinateCoefficient q) = 1 := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  have hf := summable_ordinateCoefficient hq
  have hf' : Summable (fun n : ℕ ↦ q ^ (n + 1) / (1 - q ^ (2 * (n + 1) + 1))) :=
    hf.comp_injective Nat.succ_injective
  have ht : valuation K (∑' n : ℕ, q ^ (n + 1) / (1 - q ^ (2 * (n + 1) + 1))) < 1 := by
    apply (valuation_tsum_le (r := valuation K q) hf' (fun n ↦ ?_)).trans_lt hq
    have hp : valuation K (q ^ (2 * (n + 1) + 1)) < 1 := by
      rw [map_pow]
      exact pow_lt_one₀ zero_le hq (by omega)
    rw [map_div₀, (valuation K).map_one_sub_of_lt hp, div_one, map_pow]
    simpa only [pow_one] using pow_le_pow_right_of_le_one' hq.le (Nat.le_add_left 1 n)
  have hzero : valuation K (q ^ 0 / (1 - q ^ (2 * 0 + 1))) = 1 := by
    simp only [pow_zero, mul_zero, zero_add, pow_one, map_div₀, map_one,
      (valuation K).map_one_sub_of_lt hq, div_one]
  rw [ordinateCoefficient, hf.tsum_eq_zero_add,
    (valuation K).map_add_eq_of_lt_left (ht.trans_eq hzero.symm), hzero]

/-- In characteristic two the ordinate is affine-linear in a square root of the period. -/
theorem tateY_of_sq_eq_of_two_eq_zero {q u : K} (hq0 : q ≠ 0)
    (hq : valuation K q < 1) (huq : u ^ 2 = q) (h2 : (2 : K) = 0) :
    tateY u q = -u * ordinateCoefficient q + tateCorrection q := by
  rw [tateY_of_sq_eq hq0 hq huq, ordinateCoefficient, ← tsum_mul_left, ← tsum_neg]
  congr 1
  apply tsum_congr
  intro n
  have he : (1 - q ^ n * u) ^ 2 = 1 - q ^ (2 * n + 1) := by
    have hp : q ^ (2 * n + 1) = (q ^ n * u) ^ 2 := by
      rw [mul_pow, huq]
      ring
    rw [hp]
    linear_combination ((q ^ n * u) ^ 2 - q ^ n * u) * h2
  simp only [xTerm, he, neg_mul]
  ring
/-- Continuous field morphisms commute with the ordinate coefficient. -/
theorem map_ordinateCoefficient {L : Type*} [Field L] [TopologicalSpace L] [T2Space L]
    (f : K →+* L) (hf : Continuous f) {q : K} (hq : valuation K q < 1) :
    f (ordinateCoefficient q) = ordinateCoefficient (f q) := by
  rw [ordinateCoefficient, (summable_ordinateCoefficient hq).map_tsum f hf]
  simp only [ordinateCoefficient, map_div₀, map_sub, map_one, map_pow]
end TateCurve

open ValuativeRel
open scoped WeierstrassCurve.Affine
namespace TateCurve
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
/-- Over any extension, a parameter above the abscissa of a rational point has rational ordinate. -/
theorem exists_ordinate_of_tateX_eq (q : Kˣ) (hq : valuation K (q : K) < 1) (u : Lˣ)
    (hu : u ∉ Subgroup.zpowers (Units.map (algebraMap K L).toMonoidHom q))
    {x y : K} (hxy : (WeierstrassCurve.tateCurve (q : K)).toAffine.Nonsingular x y)
    (hx : tateX (u : L) (algebraMap K L q) = algebraMap K L x) :
    ∃ z : K, tateY (u : L) (algebraMap K L q) = algebraMap K L z := by
  let E := WeierstrassCurve.tateCurve (q : K)
  have hP : (E⁄L).Nonsingular (algebraMap K L x) (algebraMap K L y) :=
    (E.toAffine.map_nonsingular (algebraMap K L).injective x y).mpr hxy
  have hQ := tateCoordinates_nonsingular (Units.map (algebraMap K L).toMonoidHom q) u
    (valuation_algebraMap_lt_one hq) hu
  have hQ' : (E⁄L).Nonsingular (tateX (u : L) (algebraMap K L q))
      (tateY (u : L) (algebraMap K L q)) := by
    simpa [E, WeierstrassCurve.tateCurve_baseChange (q : K) hq] using hQ
  rcases WeierstrassCurve.Affine.Y_eq_of_X_eq hQ'.1 hP.1 hx with h | h
  · exact ⟨y, h⟩
  · refine ⟨-y - x, ?_⟩
    simpa [WeierstrassCurve.Affine.negY, E, WeierstrassCurve.tateCurve,
      WeierstrassCurve.baseChange] using h
end TateCurve
namespace TateCurve
open Polynomial ValuativeRel
universe u
variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
/-- The inseparable interior quadratic splits by recovering its root from the ordinate. -/
theorem interior_lift_of_two_eq_zero (q : Kˣ) (hq : valuation K (q : K) < 1)
    (x y : K) (hxy : (WeierstrassCurve.tateCurve (q : K)).toAffine.Nonsingular x y)
    (hseries : (∑' n : ℕ, xPair ((q : K) ^ (2 * n) * q) ((q : K) ^ n * 0)) -
      2 * tateCorrection (q : K) = x)
    (h2 : (2 : K) = 0) : ∃ u : K, u ^ 2 - 0 * u + q = 0 := by
  classical
  let f := parameterQuadratic (0 : K) q
  let L := f.SplittingField
  obtain ⟨v, top, hloc, hext, hc, -⟩ := exists_localField_extension K L
  let := v
  let := top
  let := hloc
  let := hext
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  obtain ⟨u, hu⟩ := (SplittingField.splits f).exists_eval_eq_zero (by
    intro hd
    have hn := natDegree_eq_of_degree_eq_some hd
    have he : (Polynomial.map (algebraMap K L) f).natDegree = 2 := by
      rw [natDegree_map, natDegree_parameterQuadratic]
    have hh : (2 : ℕ) = 0 := by convert! he.symm.trans hn using 1
    omega)
  have hur : aeval u f = 0 := by simpa only [eval_map, aeval_def] using hu
  have hroot : u ^ 2 - 0 * u + algebraMap K L (q : K) = 0 := by
    change (aeval u) (Polynomial.X ^ 2 - C (0 : K) * Polynomial.X + C (q : K)) = 0 at hur
    simpa only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, map_zero] using hur
  have h2L : (2 : L) = 0 := by simpa only [map_ofNat, map_zero] using congrArg (algebraMap K L) h2
  have huq : u ^ 2 = algebraMap K L (q : K) := by
    linear_combination hroot - algebraMap K L (q : K) * h2L
  have hq' := valuation_algebraMap_lt_one (l := L) hq
  have hq0 : algebraMap K L (q : K) ≠ 0 := (_root_.map_ne_zero _).mpr q.ne_zero
  have ht : valuation K (0 : K) < 1 := by simp
  have ht' : valuation L (0 : L) < 1 := by simp
  obtain ⟨hu0, hult, hqu, -⟩ := interior_quadratic_root_bounds hq0 hq' ht' hroot
  have hmem : Units.mk0 u hu0 ∉
      Subgroup.zpowers (Units.map (algebraMap K L).toMonoidHom q) := by
    apply not_mem_zpowers_of_mem_annulus _ (Units.mk0 u hu0) hq'
      (by intro h; change u = 1 at h; simp [h] at hult) _ hult.le
    change valuation L (algebraMap K L (q : K)) < valuation L u
    exact (div_lt_one₀ (zero_lt_iff.mpr ((valuation L).ne_zero_iff.mpr hu0))).mp
      (by simpa only [map_div₀] using hqu)
  have hx : tateX u (algebraMap K L q) = algebraMap K L x := by
    apply tateX_eq_of_interior_quadratic hq0 hq' ht' _ hroot
    have he := congrArg (algebraMap K L) hseries
    simpa only [map_sub, map_mul, map_ofNat, map_zero,
      map_tsum_xPair _ hc hq hq ht,
      map_tateCorrection _ hc (tendsto_pow_nhds_zero hq)] using he
  obtain ⟨z, hz⟩ := exists_ordinate_of_tateX_eq q hq (Units.mk0 u hu0) hmem hxy hx
  have hY := tateY_of_sq_eq_of_two_eq_zero hq0 hq' huq h2L
  have hA0 : ordinateCoefficient (q : K) ≠ 0 := by
    intro h
    have he := valuation_ordinateCoefficient hq
    simp [h] at he
  let w : K := (tateCorrection (q : K) - z) / ordinateCoefficient (q : K)
  have hw : algebraMap K L w = u := by
    have hA0' : ordinateCoefficient (algebraMap K L (q : K)) ≠ 0 := by
      rw [← map_ordinateCoefficient _ hc hq]
      exact (_root_.map_ne_zero _).mpr hA0
    change algebraMap K L ((tateCorrection (q : K) - z) / ordinateCoefficient (q : K)) = u
    rw [map_div₀, map_sub, map_ordinateCoefficient _ hc hq,
      map_tateCorrection _ hc (tendsto_pow_nhds_zero hq), div_eq_iff hA0']
    change tateY u (algebraMap K L (q : K)) = algebraMap K L z at hz
    linear_combination hz - hY
  refine ⟨w, (algebraMap K L).injective ?_⟩
  simpa only [map_add, map_sub, map_mul, map_pow, map_zero, hw] using hroot
end TateCurve
