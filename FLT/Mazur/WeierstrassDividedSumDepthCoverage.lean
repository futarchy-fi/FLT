/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOwnSumDepthResidue
public import FLT.Mazur.WeierstrassDividedSumDepthSmoothOutput
public import FLT.Mazur.WeierstrassDividedExactCoefficientDepth

/-!
# Closed-fiber coverage for the actual sum-depth source

The stronger bound twice the sum depth below the node depth kills the
sum-depth constant. Every closed-fiber prime of the constructed source
then has a smooth output, without an additional output condition.
-/

@[expose] public noncomputable section
open AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsNoetherianRing R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k l m n : ℕ} (D : SplitNodeDepth W π m)
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hd : k + l ≤ n)
  (dd : Data W π (k + k)) (ee : Data W π (l + l)) (h2 : W.a₂ = 0)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "hπ" => D.uniformizer_ne_zero
local notation "z" => data ⟨k + l, Nat.lt_succ_of_le hd⟩
local notation "T" => SumDepthSourceRing d e a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "x₁" => ((j).comp a) (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "y₁" => ((j).comp a) (y W (π ^ k) d.b3 d.b4 d.b6)
local notation "x₂" => ((j).comp c) (x W (π ^ l) e.b3 e.b4 e.b6)
local notation "y₂" => ((j).comp c) (y W (π ^ l) e.b3 e.b4 e.b6)
local notation "α" => algebraMap R T W.a₁
local notation "V" => sumDepthSmoothOpen hπ d e hkl data hd dd ee h2 a c

/-- All closed-fiber points of the actual source have smooth sum-depth outputs. -/
theorem sumDepthSmoothOpen_closed_mem (hk : 0 < k) (hlt : k < l)
    (hm : 2 * (k + l) < m) (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal) : p ∈ V := by
  let K := p.asIdeal.ResidueField
  let ρ : T →ₐ[R] K := IsScalarTower.toAlgHom R T K
  have van (b : R) (hb : b ∈ maximalIdeal R) : algebraMap R K b = 0 := by
    rw [D.maximalIdeal_eq, Ideal.mem_span_singleton] at hb
    obtain ⟨v, hv⟩ := hb
    rw [IsScalarTower.algebraMap_apply R T K]
    apply Ideal.algebraMap_residueField_eq_zero.mpr
    rw [hv, map_mul]
    exact p.asIdeal.mul_mem_right _ hp
  have hπ0 : algebraMap R K π = 0 :=
    van π (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
  have hs : algebraMap R K (π ^ k) = 0 := by
    rw [map_pow, hπ0, zero_pow (by omega)]
  have ht : algebraMap R K (π ^ (l - k)) = 0 := by
    rw [map_pow, hπ0, zero_pow (by omega)]
  have h3 := van d.b3 (Ideal.pow_le_self (by omega)
    (divided_linear_deep_mem D d (by omega)).1)
  have h4 := van dd.b4 (Ideal.pow_le_self (by omega)
    (divided_linear_deep_mem D dd (by omega)).2)
  have hz3 := van (z).b3 (Ideal.pow_le_self (by
    change m + 1 - (0 + (k + l)) ≠ 0
    omega) (divided_linear_deep_mem D z (by change 0 + (k + l) ≤ m + 1; omega)).1)
  have hz6 := van (z).b6 (Ideal.pow_le_self (by
    change m - 2 * (0 + (k + l)) ≠ 0
    omega) (divided_constant_exact_depth D z (by change 2 * (0 + (k + l)) ≤ m; omega)).1)
  have hn := sumDepthSourceOutputAt_residue_vertical d e a c hπ hkl dd ee z
    (Nat.zero_add _) h2 ρ hs ht h3 h4 hz3 hz6 (D.a₁_unit.map (algebraMap R K)).ne_zero
  apply sumDepthSmoothOpen_mem hπ d e hkl data hd dd ee h2 a c p
  exact fun h => hn (Ideal.algebraMap_residueField_eq_zero.mpr h)

/-- The resulting closed-fiber outputs belong to an open of the full original input scheme. -/
theorem sumDepthDomain_closed_image (hk : 0 < k) (hlt : k < l)
    (hm : 2 * (k + l) < m) (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal) :
    PrimeSpectrum.comap (algebraMap S T) p ∈
      sumDepthDomain hπ d e hkl data hd dd ee h2 a c :=
  sumDepthDomain_image hπ d e hkl data hd dd ee h2 a c p
    (sumDepthSmoothOpen_closed_mem D d e hkl data hd dd ee h2 a c hk hlt hm p hp)

/-- Positive punctured branches of the full input scheme lie in the constructed output domain. -/
theorem sumDepthDomain_positive_mem (hk : 0 < k) (hlt : k < l)
    (hm : 2 * (k + l) < m) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal)
    (hx : a (x W (π ^ k) d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hu : c (x W (π ^ l) e.b3 e.b4 e.b6) ∉ p.asIdeal)
    (hy : a (y W (π ^ k) d.b3 d.b4 d.b6) ∈ p.asIdeal)
    (hv : c (y W (π ^ l) e.b3 e.b4 e.b6) ∈ p.asIdeal) :
    p ∈ sumDepthDomain hπ d e hkl data hd dd ee h2 a c := by
  let K := p.asIdeal.ResidueField
  let ρ : S →ₐ[R] K := IsScalarTower.toAlgHom R S K
  have van (b : R) (hb : b ∈ maximalIdeal R) : algebraMap R K b = 0 := by
    rw [D.maximalIdeal_eq, Ideal.mem_span_singleton] at hb
    obtain ⟨v, hv⟩ := hb
    rw [IsScalarTower.algebraMap_apply R S K]
    apply Ideal.algebraMap_residueField_eq_zero.mpr
    rw [hv, map_mul]
    exact p.asIdeal.mul_mem_right _ hp
  have hπ0 : algebraMap R K π = 0 :=
    van π (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
  have ht : algebraMap R K (π ^ (l - k)) = 0 := by
    rw [map_pow, hπ0, zero_pow (by omega)]
  have h3 := van d.b3 (Ideal.pow_le_self (by omega)
    (divided_linear_deep_mem D d (by omega)).1)
  have he3 := van e.b3 (Ideal.pow_le_self (by omega)
    (divided_linear_deep_mem D e (by omega)).1)
  have hx0 : ρ (a (x W (π ^ k) d.b3 d.b4 d.b6)) ≠ 0 :=
    fun h => hx (Ideal.algebraMap_residueField_eq_zero.mp h)
  have hu0 : ρ (c (x W (π ^ l) e.b3 e.b4 e.b6)) ≠ 0 :=
    fun h => hu (Ideal.algebraMap_residueField_eq_zero.mp h)
  have hy0 : ρ (a (y W (π ^ k) d.b3 d.b4 d.b6)) = 0 :=
    Ideal.algebraMap_residueField_eq_zero.mpr hy
  have hv0 : ρ (c (y W (π ^ l) e.b3 e.b4 e.b6)) = 0 :=
    Ideal.algebraMap_residueField_eq_zero.mpr hv
  have ha := (D.a₁_unit.map (algebraMap R K)).ne_zero
  have hden : ρ (sumDepthSourceDenominator d e a c) ≠ 0 := by
    simp only [sumDepthSourceDenominator, dividedTangentBranchFactor, map_mul, map_sub,
      map_add, AlgHom.commutes, ht, hy0, hv0, h3, he3, zero_mul, sub_zero,
      zero_add, add_zero]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hx0 (mul_ne_zero hx0 hu0))
      (mul_ne_zero ha hx0)) (mul_ne_zero ha hu0)
  have hn : sumDepthSourceDenominator d e a c ∉ p.asIdeal :=
    fun h => hden (Ideal.algebraMap_residueField_eq_zero.mpr h)
  obtain ⟨q, hq⟩ := (PrimeSpectrum.localization_away_comap_range T
    (sumDepthSourceDenominator d e a c)).ge hn
  have hpq : algebraMap R T π ∈ q.asIdeal := by
    rw [IsScalarTower.algebraMap_apply R S T]
    change algebraMap R S π ∈ (PrimeSpectrum.comap (algebraMap S T) q).asIdeal
    rwa [hq]
  have h := sumDepthDomain_closed_image D d e hkl data hd dd ee h2 a c hk hlt hm q hpq
  rwa [hq] at h

end FLT.Mazur.WeierstrassDividedDepth
