/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalReflectedSecantResidue
public import FLT.Mazur.WeierstrassDividedNodalReflectedNegative

/-!
# Positive equal-depth coverage away from the diagonal

On positive punctured branches the normalized source denominator has only
one additional factor: the original secant difference. Keeping that factor
explicit proves coverage at equal depths whenever the abscissae differ.
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
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hd : m - k - l ≤ n)
  (hl : 2 * l ≤ m) (hm : m ≤ k + 2 * l)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "hπ" => D.uniformizer_ne_zero
local notation "z" => data ⟨m - k - l, Nat.lt_succ_of_le hd⟩
local notation "σ" => nodalSecondShear D (m - 2 * l)
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
local notation "V" => nodalReflectedSmoothOpen D d e hkl data hd hl hm a c

/-- Positive punctured branches of the full input scheme lie in the constructed output domain. -/
theorem nodalReflectedDomain_positive_secant_mem (hk : 0 < k)
    (hltm : 2 * l < m) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal)
    (hδ : a (x W (π ^ k) d.b3 d.b4 d.b6) - algebraMap R S (π ^ (l - k)) *
      c (x W (π ^ l) e.b3 e.b4 e.b6) ∉ p.asIdeal)
    (hx : a (x W (π ^ k) d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hu : c (x W (π ^ l) e.b3 e.b4 e.b6) ∉ p.asIdeal)
    (hy : a (y W (π ^ k) d.b3 d.b4 d.b6) ∈ p.asIdeal)
    (hv : c (y W (π ^ l) e.b3 e.b4 e.b6) ∈ p.asIdeal) :
    p ∈ nodalReflectedDomain D d e hkl data hd hl hm a c := by
  let K := p.asIdeal.ResidueField
  let ρ : S →ₐ[R] K := IsScalarTower.toAlgHom R S K
  have van (b : R) (hb : b ∈ maximalIdeal R) : algebraMap R K b = 0 := by
    rw [D.maximalIdeal_eq, Ideal.mem_span_singleton] at hb
    obtain ⟨v, hv⟩ := hb
    rw [IsScalarTower.algebraMap_apply R S K]
    apply Ideal.algebraMap_residueField_eq_zero.mpr
    rw [hv, map_mul]
    exact p.asIdeal.mul_mem_right _ hp
  have h3 := van d.b3 (Ideal.pow_le_self (by omega)
    (divided_linear_deep_mem D d (by omega)).1)
  have he3 := van e.b3 (Ideal.pow_le_self (by omega)
    (divided_linear_deep_mem D e (by omega)).1)
  have hδ0 : ρ (a (x W (π ^ k) d.b3 d.b4 d.b6)) -
      algebraMap R K (π ^ (l - k)) * ρ (c (x W (π ^ l) e.b3 e.b4 e.b6)) ≠ 0 := by
    simpa only [map_sub, map_mul, AlgHom.commutes] using
      (show ρ (a (x W (π ^ k) d.b3 d.b4 d.b6) - algebraMap R S (π ^ (l - k)) *
        c (x W (π ^ l) e.b3 e.b4 e.b6)) ≠ 0 from
        fun h => hδ (Ideal.algebraMap_residueField_eq_zero.mp h))
  have hx0 : ρ (a (x W (π ^ k) d.b3 d.b4 d.b6)) ≠ 0 :=
    fun h => hx (Ideal.algebraMap_residueField_eq_zero.mp h)
  have hu0 : ρ (c (x W (π ^ l) e.b3 e.b4 e.b6)) ≠ 0 :=
    fun h => hu (Ideal.algebraMap_residueField_eq_zero.mp h)
  have hy0 : ρ (a (y W (π ^ k) d.b3 d.b4 d.b6)) = 0 :=
    Ideal.algebraMap_residueField_eq_zero.mpr hy
  have hv0 : ρ (c (y W (π ^ l) e.b3 e.b4 e.b6)) = 0 :=
    Ideal.algebraMap_residueField_eq_zero.mpr hv
  have ha := (D.a₁_unit.map (algebraMap R K)).ne_zero
  have hσ := van σ (nodalSecondShear_mem D (m - 2 * l))
  have hden : ρ (sumDepthSourceDenominator sd se a' c') ≠ 0 := by
    simp only [sumDepthSourceDenominator, branchShearInput_x,
      branchShearInput_y, dividedTangentBranchFactor, (rootShearCurve_coefficients σ).1,
      map_mul, map_sub, map_ofNat,
      map_add, AlgHom.commutes, hy0, hv0, h3, he3, hσ, zero_mul, mul_zero, sub_zero,
      zero_add, add_zero]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hδ0 (mul_ne_zero hx0 hu0))
      (mul_ne_zero ha hx0)) (mul_ne_zero ha hu0)
  have hn : sumDepthSourceDenominator sd se a' c' ∉ p.asIdeal :=
    fun h => hden (Ideal.algebraMap_residueField_eq_zero.mpr h)
  obtain ⟨q, hq⟩ := (PrimeSpectrum.localization_away_comap_range T
    (sumDepthSourceDenominator sd se a' c')).ge hn
  have hpq : algebraMap R T π ∈ q.asIdeal := by
    rw [IsScalarTower.algebraMap_apply R S T]
    change algebraMap R S π ∈ (PrimeSpectrum.comap (algebraMap S T) q).asIdeal
    rwa [hq]
  have h := nodalReflectedDomain_secant_closed_image D d e hkl hl hm a c data hd hk hltm q hpq
  rwa [hq] at h

local notation "na" => branchNegativeInput W (π ^ k) d.b3 d.b4 d.b6 a
local notation "nc" => branchNegativeInput W (π ^ l) e.b3 e.b4 e.b6 c

/-- Negative punctured branches have actual smooth outputs on the unchanged full input spectrum. -/
theorem nodalReflectedNegativeDomain_secant_mem (hk : 0 < k)
    (hltm : 2 * l < m) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal)
    (hδ : a (x W (π ^ k) d.b3 d.b4 d.b6) - algebraMap R S (π ^ (l - k)) *
      c (x W (π ^ l) e.b3 e.b4 e.b6) ∉ p.asIdeal)
    (hx : a (x W (π ^ k) d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hu : c (x W (π ^ l) e.b3 e.b4 e.b6) ∉ p.asIdeal)
    (hy : dividedTangentBranchFactor W (π ^ k) d.b3 d.b4 d.b6 a ∈ p.asIdeal)
    (hv : dividedTangentBranchFactor W (π ^ l) e.b3 e.b4 e.b6 c ∈ p.asIdeal) :
    p ∈ nodalReflectedNegativeDomain D d e hkl data hd hl hm a c := by
  apply nodalReflectedDomain_positive_secant_mem D d e hkl data hd hl hm
    na nc hk hltm p hp
  · simpa only [branchNegativeInput_x] using hδ
  · simpa only [branchNegativeInput_x] using hx
  · simpa only [branchNegativeInput_x] using hu
  · have he : na (y W (π ^ k) d.b3 d.b4 d.b6) =
        -dividedTangentBranchFactor W (π ^ k) d.b3 d.b4 d.b6 a := by
      rw [branchNegativeInput_y, dividedTangentBranchFactor]
      ring
    rw [he]
    exact p.asIdeal.neg_mem hy
  · have he : nc (y W (π ^ l) e.b3 e.b4 e.b6) =
        -dividedTangentBranchFactor W (π ^ l) e.b3 e.b4 e.b6 c := by
      rw [branchNegativeInput_y, dividedTangentBranchFactor]
      ring
    rw [he]
    exact p.asIdeal.neg_mem hv

end FLT.Mazur.WeierstrassDividedDepth
