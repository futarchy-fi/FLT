/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.TateCurve.Equation

import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

/-!
# Local-field expansions of Tate coordinates

The two tails of the integer-indexed coordinates expand geometrically when
`|qu| < 1` and `|q/u| < 1`. Regrouping by powers of `q` gives the integral formal
coordinate series, which satisfy the Tate equation.
-/

@[expose] public section

open ValuativeRel
open scoped PowerSeries

namespace TateCurve

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Integer-weighted Lambert double series converge whenever both `q` and `qu`
lie in the open unit disc. -/
theorem summable_lambert_coordinate (c : ℕ → ℤ) {q u : K}
    (hq : valuation K q < 1) (hqu : valuation K (q * u) < 1) :
    Summable (fun p : ℕ+ × ℕ+ ↦ (c p.2 : K) * u ^ (p.2 : ℕ) *
      q ^ ((p.1 : ℕ) * (p.2 : ℕ))) := by
  let r := if valuation K u ≤ 1 then q else q * u
  have hr : valuation K r < 1 := by
    dsimp [r]
    split_ifs <;> assumption
  refine summable_of_valuation_le_pow hr (fun p ↦ (p.1 : ℕ) * (p.2 : ℕ))
    (fun N ↦ ?_) (fun p ↦ ?_)
  · refine (((Set.finite_Iio N).preimage PNat.coe_injective.injOn).prod
      ((Set.finite_Iio N).preimage PNat.coe_injective.injOn)).subset fun p hp ↦ ?_
    exact ⟨lt_of_le_of_lt (Nat.le_mul_of_pos_right _ p.2.pos) hp,
      lt_of_le_of_lt (Nat.le_mul_of_pos_left _ p.1.pos) hp⟩
  · simp only [map_mul, map_pow]
    calc valuation K (c p.2 : K) * valuation K u ^ (p.2 : ℕ) *
          valuation K q ^ ((p.1 : ℕ) * (p.2 : ℕ))
        ≤ valuation K u ^ (p.2 : ℕ) * valuation K q ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
          exact mul_le_mul_left
            ((mul_le_mul_left (valuation_intCast_le_one (R := K) (c p.2)) _).trans_eq
              (one_mul _)) _
      _ ≤ valuation K r ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
        dsimp [r]
        split_ifs with hu
        · exact mul_le_of_le_one_left' (pow_le_one₀ zero_le hu)
        · rw [map_mul, mul_comm (valuation K q), mul_pow]
          exact mul_le_mul_left
            (pow_le_pow_right₀ (le_of_lt (lt_of_not_ge hu))
              (Nat.le_mul_of_pos_left _ p.1.pos)) _

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The positive powers of `q` preserve the open-unit-disc condition for `q*u`. -/
theorem valuation_pow_mul_lt_one {q u : K} (hq : valuation K q < 1)
    (hqu : valuation K (q * u) < 1) (n : ℕ+) :
    valuation K (q ^ (n : ℕ) * u) < 1 := by
  rw [← Nat.sub_add_cancel n.pos, pow_succ, mul_assoc, map_mul, map_pow]
  exact (mul_le_of_le_one_left' (pow_le_one₀ zero_le hq.le)).trans_lt hqu

/-- Regroup an unconditionally convergent Lambert double series by its divisor pairs. -/
theorem hasSum_divisor_coordinates (g : ℕ → K) {q a : K}
    (h : HasSum (fun p : ℕ+ × ℕ+ ↦ g p.2 * q ^ ((p.1 : ℕ) * (p.2 : ℕ))) a) :
    HasSum (fun n : ℕ+ ↦ (∑ d ∈ (n : ℕ).divisors, g d) * q ^ (n : ℕ)) a := by
  apply ((sigmaAntidiagonalEquivProd.hasSum_iff).mpr h).sigma
  intro n
  have hs := hasSum_fintype (fun c : ((n : ℕ).divisorsAntidiagonal) ↦
    (g c.1.2 * q ^ (c.1.1 * c.1.2)))
  have hv : (∑ c : ((n : ℕ).divisorsAntidiagonal), g c.1.2 * q ^ (c.1.1 * c.1.2)) =
      (∑ d ∈ (n : ℕ).divisors, g d) * q ^ (n : ℕ) := by
    rw [Finset.univ_eq_attach,
      Finset.sum_attach ((n : ℕ).divisorsAntidiagonal) (fun p ↦ g p.2 * q ^ (p.1 * p.2)),
      show (∑ p ∈ (n : ℕ).divisorsAntidiagonal, g p.2 * q ^ (p.1 * p.2)) =
          ∑ p ∈ (n : ℕ).divisorsAntidiagonal, g p.2 * q ^ (n : ℕ) from
        Finset.sum_congr rfl fun p hp ↦ by rw [(Nat.mem_divisorsAntidiagonal.mp hp).1],
      ← Finset.sum_mul, Nat.sum_divisorsAntidiagonal' (f := fun _ d ↦ g d)]
  rw [hv] at hs
  refine hs.congr_fun fun c ↦ ?_
  simp only [Function.comp_apply, sigmaAntidiagonalEquivProd, Equiv.coe_fn_mk,
    divisorsAntidiagonalFactors, PNat.mk_coe]

/-- Remove the zero term from a convergent series when it vanishes. -/
private theorem hasSum_pnat_coordinates {f : ℕ → K} {a : K}
    (h : HasSum f a) (h0 : f 0 = 0) : HasSum (fun n : ℕ+ ↦ f n) a := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  rw [← h.tsum_eq, ← tsum_zero_pnat_eq_tsum_nat h.summable, h0, zero_add]
  exact (h.summable.comp_injective PNat.coe_injective).hasSum

/-- Restore the zero term to a convergent series indexed by positive integers. -/
private theorem hasSum_nat_coordinates {f : ℕ → K} {a : K}
    (h : HasSum (fun n : ℕ+ ↦ f n) a) : HasSum f (a + f 0) := by
  have hn : HasSum (fun n : ℕ ↦ f (n + 1)) a := by
    simpa only [Function.comp_def, Equiv.pnatEquivNat_symm_apply, PNat.mk_coe,
      Nat.succPNat_coe] using
      Equiv.pnatEquivNat.symm.hasSum_iff.mpr h
  simpa using (hasSum_nat_add_iff (f := f) 1).mp hn

/-- Geometric row expansions determine the sum of a Lambert double series. -/
theorem hasSum_lambert_coordinate (c : ℕ → ℤ) (g : K → K) {q u : K}
    (hq : valuation K q < 1) (hqu : valuation K (q * u) < 1)
    (hg : ∀ v : K, valuation K v < 1 →
      HasSum (fun m : ℕ+ ↦ (c m : K) * v ^ (m : ℕ)) (g v)) :
    HasSum (fun p : ℕ+ × ℕ+ ↦ (c p.2 : K) * u ^ (p.2 : ℕ) *
      q ^ ((p.1 : ℕ) * (p.2 : ℕ))) (∑' n : ℕ+, g (q ^ (n : ℕ) * u)) := by
  have hs := summable_lambert_coordinate c hq hqu
  have hrow (n : ℕ+) : HasSum (fun m : ℕ+ ↦ (c m : K) * u ^ (m : ℕ) *
      q ^ ((n : ℕ) * (m : ℕ))) (g (q ^ (n : ℕ) * u)) := by
    refine (hg _ (valuation_pow_mul_lt_one hq hqu n)).congr_fun fun m ↦ ?_
    rw [mul_pow, ← pow_mul]
    ring
  simpa only [hs.tsum_prod' (fun n ↦ (hrow n).summable),
    tsum_congr (fun n ↦ (hrow n).tsum_eq)] using hs.hasSum

/-- Split a convergent integer-indexed series into its zero term and its two tails. -/
private theorem tsum_int_coordinates {f : ℤ → K} (hf : Summable f) :
    ∑' n : ℤ, f n = f 0 + ∑' n : ℕ+, f (n : ℤ) + ∑' n : ℕ+, f (-(n : ℤ)) := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  have hp : Summable (fun n : ℕ ↦ f n) := hf.comp_injective Nat.cast_injective
  have hn : Summable (fun n : ℕ ↦ f (-((n : ℤ) + 1))) :=
    (hf.comp_injective (fun a b h ↦ (Int.negSucc.inj h : a = b))).congr fun n ↦ by
      simp only [Function.comp_apply, Int.negSucc_eq]
  have he : (∑' n : ℕ, f (-((n : ℤ) + 1))) = ∑' n : ℕ+, f (-(n : ℤ)) := by
    rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ f (-(n : ℤ)))]
    exact tsum_congr fun n ↦ by congr 1
  rw [tsum_of_nat_of_neg_add_one hp hn, ← tsum_zero_pnat_eq_tsum_nat hp, he]
  rfl

/-- The formal `x`-coordinate expansion sums to the integer-indexed Tate coordinate
on the annulus where both tails admit their geometric expansions. -/
theorem hasSum_integralX {q u : K} (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq : valuation K q < 1) (hqu : valuation K (q * u) < 1)
    (hqui : valuation K (q * u⁻¹) < 1) :
    HasSum (fun n ↦ PowerSeries.coeff n (integralX u u⁻¹ (1 - u)⁻¹) * q ^ n)
      (tateX u q) := by
  have hg (v : K) (hv : valuation K v < 1) :
      HasSum (fun m : ℕ+ ↦ ((m : ℕ) : K) * v ^ (m : ℕ)) (xTerm v) :=
    hasSum_pnat_coordinates (hasSum_nat_mul_geometric_of_valuation_lt_one hv) (by simp)
  have ha := hasSum_lambert_coordinate (fun n ↦ (n : ℤ)) xTerm hq hqu
    (fun v hv ↦ by simpa only [Int.cast_natCast] using hg v hv)
  have hb := hasSum_lambert_coordinate (fun n ↦ (n : ℤ)) xTerm hq hqui
    (fun v hv ↦ by simpa only [Int.cast_natCast] using hg v hv)
  have hc := hasSum_lambert_coordinate (fun n ↦ (n : ℤ)) xTerm hq
    (show valuation K (q * 1) < 1 by simpa using hq)
    (fun v hv ↦ by simpa only [Int.cast_natCast] using hg v hv)
  have hcval : (∑' n : ℕ+, xTerm (q ^ (n : ℕ) * 1)) = tateCorrection q := by
    simp only [mul_one, tateCorrection]
    exact tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ xTerm (q ^ n))
  rw [hcval] at hc
  have hd := hasSum_divisor_coordinates (q := q) (fun d ↦ (d : K) * (u ^ d + u⁻¹ ^ d - 2))
    (((ha.add hb).sub (hc.mul_left 2)).congr_fun fun p ↦ by push_cast; ring)
  have hfull := hasSum_nat_coordinates
    (f := fun n ↦ PowerSeries.coeff n (integralX u u⁻¹ (1 - u)⁻¹) * q ^ n)
    (hd.congr_fun fun n ↦ by
      simp only [integralX, map_add, PowerSeries.coeff_C, PowerSeries.coeff_mk,
        ite_eq_right n.pos.ne', zero_add])
  convert hfull using 1
  rw [tateX, tsum_int_coordinates (summable_tate_x_of_valuation_lt_one hq0 hu0 hq)]
  have hn (n : ℕ+) : xTerm (q ^ (-(n : ℤ)) * u) = xTerm (q ^ (n : ℕ) * u⁻¹) := by
    rw [show q ^ (-(n : ℤ)) * u = (q ^ (n : ℕ) * u⁻¹)⁻¹ by simp [mul_comm],
      xTerm_inv (mul_ne_zero (pow_ne_zero _ hq0) (inv_ne_zero hu0))]
  rw [tsum_congr hn]
  simp only [zpow_zero, one_mul, zpow_natCast, integralX, map_add,
    PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_mk, Nat.divisors_zero, Finset.sum_empty, add_zero,
    pow_zero, mul_one, xTerm, inv_pow, div_eq_mul_inv]
  ring

/-- The formal `y`-coordinate expansion sums to the integer-indexed Tate coordinate
on the annulus where both tails admit their geometric expansions. -/
theorem hasSum_integralY {q u : K} (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq : valuation K q < 1) (hqu : valuation K (q * u) < 1)
    (hqui : valuation K (q * u⁻¹) < 1) :
    HasSum (fun n ↦ PowerSeries.coeff n (integralY u u⁻¹ (1 - u)⁻¹) * q ^ n)
      (tateY u q) := by
  have hg (v : K) (hv : valuation K v < 1) :
      HasSum (fun m : ℕ+ ↦ ((m : ℕ).choose 2 : K) * v ^ (m : ℕ)) (yTerm v) :=
    hasSum_pnat_coordinates (hasSum_choose_two_geometric_of_valuation_lt_one hv) (by simp)
  have hg' (v : K) (hv : valuation K v < 1) :
      HasSum (fun m : ℕ+ ↦ (((m : ℕ) + 1).choose 2 : K) * v ^ (m : ℕ))
        (yTerm v + xTerm v) := by
    have hx := hasSum_pnat_coordinates (hasSum_nat_mul_geometric_of_valuation_lt_one hv)
      (by simp)
    refine ((hg v hv).add hx).congr_fun fun m ↦ ?_
    rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add]
    ring
  have ha := hasSum_lambert_coordinate (fun n ↦ (n.choose 2 : ℤ)) yTerm hq hqu
    (fun v hv ↦ by simpa only [Int.cast_natCast] using hg v hv)
  have hb := hasSum_lambert_coordinate (fun n ↦ ((n + 1).choose 2 : ℤ))
    (fun v ↦ yTerm v + xTerm v) hq hqui (fun v hv ↦ by simpa only [Int.cast_natCast] using hg' v hv)
  have hc := hasSum_lambert_coordinate (fun n ↦ (n : ℤ)) xTerm hq
    (show valuation K (q * 1) < 1 by simpa using hq) (fun v hv ↦
      by simpa only [Int.cast_natCast] using
        hasSum_pnat_coordinates (hasSum_nat_mul_geometric_of_valuation_lt_one hv) (by simp))
  have hcval : (∑' n : ℕ+, xTerm (q ^ (n : ℕ) * 1)) = tateCorrection q := by
    simp only [mul_one, tateCorrection]
    exact tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ xTerm (q ^ n))
  rw [hcval] at hc
  have hd := hasSum_divisor_coordinates (q := q)
    (fun d ↦ (d.choose 2 : K) * u ^ d - ((d + 1).choose 2 : K) * u⁻¹ ^ d + d)
    (((ha.sub hb).add hc).congr_fun fun p ↦ by push_cast; ring)
  have hfull := hasSum_nat_coordinates
    (f := fun n ↦ PowerSeries.coeff n (integralY u u⁻¹ (1 - u)⁻¹) * q ^ n)
    (hd.congr_fun fun n ↦ by
      simp only [integralY, map_add, PowerSeries.coeff_C, PowerSeries.coeff_mk,
        ite_eq_right n.pos.ne', zero_add])
  convert hfull using 1
  rw [tateY, tsum_int_coordinates (summable_tate_y_of_valuation_lt_one hq0 hu0 hq)]
  have hn (n : ℕ+) : yTerm (q ^ (-(n : ℤ)) * u) =
      -(yTerm (q ^ (n : ℕ) * u⁻¹) + xTerm (q ^ (n : ℕ) * u⁻¹)) := by
    rw [show q ^ (-(n : ℤ)) * u = (q ^ (n : ℕ) * u⁻¹)⁻¹ by simp [mul_comm],
      yTerm_inv_eq (mul_ne_zero (pow_ne_zero _ hq0) (inv_ne_zero hu0))]
    ring
  rw [tsum_congr hn]
  simp only [zpow_zero, one_mul, zpow_natCast, tsum_neg, integralY,
    map_add, PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_mk, Nat.divisors_zero, Finset.sum_empty, add_zero,
    pow_zero, mul_one, yTerm, inv_pow, div_eq_mul_inv]
  ring

/-- Tate coordinates satisfy the curve equation on the annulus where the formal
expansions converge. No restriction on the field characteristic is needed. -/
theorem tateCoordinates_equation_of_annulus {q u : K} (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hu1 : u ≠ 1) (hq : valuation K q < 1) (hqu : valuation K (q * u) < 1)
    (hqui : valuation K (q * u⁻¹) < 1) :
    (WeierstrassCurve.tateCurve q).toAffine.Equation (tateX u q) (tateY u q) :=
  equation_of_hasSum_coordinates hq hu0 hu1 (hasSum_integralX hq0 hu0 hq hqu hqui)
    (hasSum_integralY hq0 hu0 hq hqu hqui)

/-- Every unit has a representative in the fundamental annulus `|q| < |u| ≤ 1`. -/
theorem exists_zpow_mul_mem_annulus (q u : Kˣ) (hq : valuation K (q : K) < 1) :
    ∃ m : ℤ, valuation K (q : K) < valuation K ((q : K) ^ m * (u : K)) ∧
      valuation K ((q : K) ^ m * (u : K)) ≤ 1 := by
  let vq : (ValueGroupWithZero K)ˣ := Units.map (valuation K).toMonoidHom q
  let vu : (ValueGroupWithZero K)ˣ := Units.map (valuation K).toMonoidHom u
  have hvq : vq < 1 := hq
  obtain ⟨m, hm, _⟩ := existsUnique_add_zpow_mem_Ioc (one_lt_inv'.mpr hvq) vu vq
  refine ⟨-m, ?_⟩
  have h1 := Units.val_lt_val.mpr hm.1
  have h2 := Units.val_le_val.mpr hm.2
  constructor
  · simpa [vq, vu, map_mul, map_zpow₀, zpow_neg, mul_comm] using h1
  · simpa [vq, vu, map_mul, map_zpow₀, zpow_neg, mul_comm] using h2

/-- The convergent Tate coordinates satisfy the Tate curve equation away from `q^ℤ`. -/
theorem tateCoordinates_equation (q u : Kˣ) (hq : valuation K (q : K) < 1)
    (hu : u ∉ Subgroup.zpowers q) :
    (WeierstrassCurve.tateCurve (q : K)).toAffine.Equation
      (tateX (u : K) (q : K)) (tateY (u : K) (q : K)) := by
  obtain ⟨m, hlow, hupp⟩ := exists_zpow_mul_mem_annulus q u hq
  have hv0 : (q : K) ^ m * (u : K) ≠ 0 := mul_ne_zero (zpow_ne_zero _ q.ne_zero) u.ne_zero
  have hv1 : (q : K) ^ m * (u : K) ≠ 1 :=
    fun h ↦ one_sub_zpow_mul_ne_zero q u hu m (by rw [h, sub_self])
  have hqu : valuation K ((q : K) * ((q : K) ^ m * (u : K))) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_right' hupp).trans_lt hq
  have hqui : valuation K ((q : K) * ((q : K) ^ m * (u : K))⁻¹) < 1 := by
    rw [map_mul, map_inv₀, ← div_eq_mul_inv]
    exact (div_lt_one₀ (zero_lt_iff.mpr ((valuation K).ne_zero_iff.mpr hv0))).mpr hlow
  simpa only [tateX_zpow_mul _ q.ne_zero, tateY_zpow_mul _ q.ne_zero] using
    tateCoordinates_equation_of_annulus q.ne_zero hv0 hv1 hq hqu hqui

end TateCurve
