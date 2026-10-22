/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalFactoredSumSmooth
public import FLT.Mazur.WeierstrassDividedExactCoefficientDepth

/-!
# Normalized factored sum-depth coverage in the original input scheme

The node depth supplies all coefficient vanishings. Every closed-fiber point
of the original localized source has a smooth sum-depth output, beyond
the sum-depth middle. Positive punctured pairs retain their own input depths.
The finite shear vanishes on the special fiber; no second coefficient is assumed zero.
-/

@[expose] public noncomputable section
open AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsNoetherianRing R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k l m n : ℕ} (D : SplitNodeDepth W π m)
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hd : k + l ≤ n)
  (hm : k + 2 * l ≤ m)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "hπ" => D.uniformizer_ne_zero
local notation "z" => data ⟨k + l, Nat.lt_succ_of_le hd⟩
local notation "σ" => nodalSecondShear D k
local notation "V₀" => rootShearCurve W σ
local notation "sd" => (⟨d.b3, d.b4 - σ * d.b3, d.b6,
  (shearData d σ).factor3, (shearData d σ).factor4,
  (shearData d σ).factor6⟩ : Data V₀ π k)
local notation "se" => (⟨e.b3, e.b4 - σ * e.b3, e.b6,
  (shearData e σ).factor3, (shearData e σ).factor4,
  (shearData e σ).factor6⟩ : Data V₀ π l)
local notation "a'" => branchShearInput W (π ^ k) d.b3 d.b4 d.b6 σ a
local notation "c'" => branchShearInput W (π ^ l) e.b3 e.b4 e.b6 σ c
local notation "T" => SumDepthSourceRing sd se a' c'

local notation "j" => IsScalarTower.toAlgHom R S T
local notation "x₁" => ((j).comp a) (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "y₁" => ((j).comp a) (y W (π ^ k) d.b3 d.b4 d.b6)
local notation "x₂" => ((j).comp c) (x W (π ^ l) e.b3 e.b4 e.b6)
local notation "y₂" => ((j).comp c) (y W (π ^ l) e.b3 e.b4 e.b6)
local notation "α" => algebraMap R T W.a₁
local notation "V" => nodalFactoredSumSmoothOpen D d e hkl data hd hm a c

/-- All closed-fiber points of the actual source have smooth sum-depth outputs. -/
theorem nodalFactoredSumSmoothOpen_closed_mem (hk : 0 < k) (hlt : k < l)
    (hmt : 2 * (k + l) < m) (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal) : p ∈ V := by
  let ρ : T →ₐ[R] p.asIdeal.ResidueField := IsScalarTower.toAlgHom R T _
  have hπ0 : algebraMap R p.asIdeal.ResidueField π = 0 := by
    rw [IsScalarTower.algebraMap_apply R T p.asIdeal.ResidueField]
    exact Ideal.algebraMap_residueField_eq_zero.mpr hp
  have hn := nodalFactoredSumSourceOutputAt_residue_vertical d e a c D hkl hm z
    (Nat.zero_add _) hk hlt hmt ρ hπ0
  apply nodalFactoredSumSmoothOpen_mem D d e hkl data hd hm a c p
  exact fun h => hn (Ideal.algebraMap_residueField_eq_zero.mpr h)

/-- The resulting closed-fiber outputs belong to an open of the full original input scheme. -/
theorem nodalFactoredSumDomain_closed_image (hk : 0 < k) (hlt : k < l)
    (hmt : 2 * (k + l) < m) (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal) :
    PrimeSpectrum.comap (algebraMap S T) p ∈
      nodalFactoredSumDomain D d e hkl data hd hm a c :=
  nodalFactoredSumDomain_image D d e hkl data hd hm a c p
    (nodalFactoredSumSmoothOpen_closed_mem D d e hkl data hd hm a c hk hlt hmt p hp)

/-- Positive punctured branches of the full input scheme lie in the constructed output domain. -/
theorem nodalFactoredSumDomain_positive_mem (hk : 0 < k) (hlt : k < l)
    (hmt : 2 * (k + l) < m) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal)
    (hx : a (x W (π ^ k) d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hu : c (x W (π ^ l) e.b3 e.b4 e.b6) ∉ p.asIdeal)
    (hy : a (y W (π ^ k) d.b3 d.b4 d.b6) ∈ p.asIdeal)
    (hv : c (y W (π ^ l) e.b3 e.b4 e.b6) ∈ p.asIdeal) :
    p ∈ nodalFactoredSumDomain D d e hkl data hd hm a c := by
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
  have hσ := van σ (nodalSecondShear_mem D k)
  have hden : ρ (sumDepthSourceDenominator sd se a' c') ≠ 0 := by
    simp only [sumDepthSourceDenominator, branchShearInput_x,
      branchShearInput_y, dividedTangentBranchFactor, (rootShearCurve_coefficients σ).1,
      map_mul, map_sub, map_ofNat,
      map_add, AlgHom.commutes, ht, hy0, hv0, h3, he3, hσ, zero_mul, mul_zero, sub_zero,
      zero_add, add_zero]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hx0 (mul_ne_zero hx0 hu0))
      (mul_ne_zero ha hx0)) (mul_ne_zero ha hu0)
  have hn : sumDepthSourceDenominator sd se a' c' ∉ p.asIdeal :=
    fun h => hden (Ideal.algebraMap_residueField_eq_zero.mpr h)
  obtain ⟨q, hq⟩ := (PrimeSpectrum.localization_away_comap_range T
    (sumDepthSourceDenominator sd se a' c')).ge hn
  have hpq : algebraMap R T π ∈ q.asIdeal := by
    rw [IsScalarTower.algebraMap_apply R S T]
    change algebraMap R S π ∈ (PrimeSpectrum.comap (algebraMap S T) q).asIdeal
    rwa [hq]
  have h := nodalFactoredSumDomain_closed_image D d e hkl data hd hm a c hk hlt hmt q hpq
  rwa [hq] at h

end FLT.Mazur.WeierstrassDividedDepth
