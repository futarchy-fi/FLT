/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReflectedTerminalIndexed
public import FLT.Mazur.WeierstrassDividedReflectedSmooth
public import FLT.Mazur.WeierstrassDividedExactCoefficientDepth

/-!
# Actual reflected coverage at even terminal depth

The unit branch factor forces the shallow ordinate to vanish. The deeper
terminal ordinate is retained in full, and its equation controls the
surviving square in the reflected numerator.
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
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hd : m - k - l ≤ n)
  (hl : 2 * l ≤ m) (hm : m ≤ k + 2 * l) (h2 : W.a₂ = 0)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "hπ" => D.uniformizer_ne_zero
local notation "z" => data ⟨m - k - l, Nat.lt_succ_of_le hd⟩
local notation "T" => SumDepthSourceRing d e a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "x₁" => ((j).comp a) (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "y₁" => ((j).comp a) (y W (π ^ k) d.b3 d.b4 d.b6)
local notation "x₂" => ((j).comp c) (x W (π ^ l) e.b3 e.b4 e.b6)
local notation "y₂" => ((j).comp c) (y W (π ^ l) e.b3 e.b4 e.b6)
local notation "α" => algebraMap R T W.a₁
local notation "V" => reflectedSmoothOpen D d e hkl data hd hl hm h2 a c

/-- Every localized closed-fiber source point has a smooth even-terminal reflected output. -/
theorem reflectedSmoothOpen_terminal_mem (hk : 0 < k) (hlt : k < l)
    (hm0 : m = 2 * l) (p : PrimeSpectrum T)
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
  have hl0 : algebraMap R K (π ^ l) = 0 := by
    rw [map_pow, hπ0, zero_pow (by omega)]
  have hdlin := divided_linear_deep_mem D d (by omega : k ≤ m + 1)
  have hd3 := van d.b3 (Ideal.pow_le_self (by omega) hdlin.1)
  have hd4 := van d.b4 (Ideal.pow_le_self (by omega) hdlin.2)
  have hd6 := van d.b6 (Ideal.pow_le_self (by omega)
    (divided_constant_exact_depth D d (by omega)).1)
  have helin := divided_linear_deep_mem D e (by omega : l ≤ m + 1)
  have he3 := van e.b3 (Ideal.pow_le_self (by omega) helin.1)
  have he4 := van e.b4 (Ideal.pow_le_self (by omega) helin.2)
  have hy : ρ y₁ = 0 := by
    have heq := equation_map W (π ^ k) d.b3 d.b4 d.b6 (ρ.comp ((j).comp a))
    simp only [AlgHom.comp_apply, hs, hd3, hd4, hd6, h2, map_zero,
      zero_mul, add_zero] at heq
    have hu := (sumDepthSource_leftUnit d e a c).map ρ
    simp only [map_add, map_mul, AlgHom.commutes, hd3, add_zero] at hu
    have he : ρ y₁ * (ρ y₁ + algebraMap R K W.a₁ * ρ x₁) = 0 := by
      simp only [AlgHom.comp_apply]
      linear_combination heq
    exact (mul_eq_zero.mp he).resolve_right hu.ne_zero
  have hz3 := van (z).b3 (Ideal.pow_le_self (by
    change m + 1 - (0 + (m - k - l)) ≠ 0
    omega) (divided_linear_deep_mem D z (by
      change 0 + (m - k - l) ≤ m + 1
      omega)).1)
  have hn := reflectedSourceOutputAt_terminal_vertical d e a c D hkl hl hm z
    (Nat.zero_add _) h2 ρ hs ht hm0 hl0 he3 he4 hz3 hy (D.a₁_unit.map (algebraMap R K)).ne_zero
  apply reflectedSmoothOpen_mem D d e hkl data hd hl hm h2 a c p
  exact fun h => hn (Ideal.algebraMap_residueField_eq_zero.mpr h)

/-- Every closed-fiber source point maps into the actual even-terminal reflected domain. -/
theorem reflectedDomain_terminal_image (hk : 0 < k) (hlt : k < l)
    (hm0 : m = 2 * l) (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal) :
    PrimeSpectrum.comap (algebraMap S T) p ∈
      reflectedDomain D d e hkl data hd hl hm h2 a c :=
  reflectedDomain_image D d e hkl data hd hl hm h2 a c p
    (reflectedSmoothOpen_terminal_mem D d e hkl data hd hl hm h2 a c hk hlt hm0 p hp)

/-- Punctured terminal inputs are covered without imposing a vanishing terminal ordinate. -/
theorem reflectedDomain_terminal_positive_mem (hk : 0 < k) (hlt : k < l)
    (hm0 : m = 2 * l) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal)
    (hx : a (x W (π ^ k) d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hu : c (x W (π ^ l) e.b3 e.b4 e.b6) ∉ p.asIdeal)
    (hy : a (y W (π ^ k) d.b3 d.b4 d.b6) ∈ p.asIdeal) :
    p ∈ reflectedDomain D d e hkl data hd hl hm h2 a c := by
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
  have hl0 : algebraMap R K (π ^ l) = 0 := by
    rw [map_pow, hπ0, zero_pow (by omega)]
  have h3 := van d.b3 (Ideal.pow_le_self (by omega)
    (divided_linear_deep_mem D d (by omega)).1)
  have helin := divided_linear_deep_mem D e (by omega : l ≤ m + 1)
  have he3 := van e.b3 (Ideal.pow_le_self (by omega) helin.1)
  have he4 := van e.b4 (Ideal.pow_le_self (by omega) helin.2)
  have h6 : algebraMap R K e.b6 ≠ 0 := by
    rw [← reflectedBranchConstant_terminal D d e hkl hl hm0]
    exact ((reflectedBranchConstant_isUnit D d hkl hl).map (algebraMap R K)).ne_zero
  have hx0 : ρ (a (x W (π ^ k) d.b3 d.b4 d.b6)) ≠ 0 :=
    fun h => hx (Ideal.algebraMap_residueField_eq_zero.mp h)
  have hu0 : ρ (c (x W (π ^ l) e.b3 e.b4 e.b6)) ≠ 0 :=
    fun h => hu (Ideal.algebraMap_residueField_eq_zero.mp h)
  have hy0 : ρ (a (y W (π ^ k) d.b3 d.b4 d.b6)) = 0 :=
    Ideal.algebraMap_residueField_eq_zero.mpr hy
  have hbranch : ρ (c (y W (π ^ l) e.b3 e.b4 e.b6)) +
      algebraMap R K W.a₁ * ρ (c (x W (π ^ l) e.b3 e.b4 e.b6)) ≠ 0 := by
    intro h
    have heq := equation_map W (π ^ l) e.b3 e.b4 e.b6 (ρ.comp c)
    simp only [AlgHom.comp_apply, hl0, he3, he4, h2, map_zero, zero_mul,
      zero_add, add_zero] at heq
    apply h6
    linear_combination ρ (c (y W (π ^ l) e.b3 e.b4 e.b6)) * h - heq
  have ha := (D.a₁_unit.map (algebraMap R K)).ne_zero
  have hden : ρ (sumDepthSourceDenominator d e a c) ≠ 0 := by
    simp only [sumDepthSourceDenominator, dividedTangentBranchFactor, map_mul, map_sub,
      map_add, AlgHom.commutes, ht, hy0, h3, he3, zero_mul, sub_zero, zero_add, add_zero]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hx0 (mul_ne_zero hx0 hu0))
      (mul_ne_zero ha hx0)) hbranch
  have hn : sumDepthSourceDenominator d e a c ∉ p.asIdeal :=
    fun h => hden (Ideal.algebraMap_residueField_eq_zero.mpr h)
  obtain ⟨q, hq⟩ := (PrimeSpectrum.localization_away_comap_range T
    (sumDepthSourceDenominator d e a c)).ge hn
  have hpq : algebraMap R T π ∈ q.asIdeal := by
    rw [IsScalarTower.algebraMap_apply R S T]
    change algebraMap R S π ∈ (PrimeSpectrum.comap (algebraMap S T) q).asIdeal
    rwa [hq]
  have h := reflectedDomain_terminal_image D d e hkl data hd hl hm h2 a c hk hlt hm0 q hpq
  rwa [hq] at h

end FLT.Mazur.WeierstrassDividedDepth
