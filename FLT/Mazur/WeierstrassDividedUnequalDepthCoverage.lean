/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedUnequalDepthResidue
public import FLT.Mazur.WeierstrassDividedUnequalDepthSmoothOutput
public import FLT.Mazur.WeierstrassDividedExactCoefficientDepth

/-!
# Opposite-branch coverage with a strictly deeper input

At strict pre-middle input depths the node data proves all coefficient
vanishing needed by the unequal-depth residue calculation. Opposite
punctured branches therefore have actual resolved smooth local outputs.
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
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hd : l - k ≤ n)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "hπ" => D.uniformizer_ne_zero
local notation "z" => data ⟨l - k, Nat.lt_succ_of_le hd⟩
local notation "T" => UnequalDepthSecantRing hπ d e hkl a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "x₁" => ((j).comp a) (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "y₁" => ((j).comp a) (y W (π ^ k) d.b3 d.b4 d.b6)
local notation "x₂" => ((j).comp c) (x W (π ^ l) e.b3 e.b4 e.b6)
local notation "y₂" => ((j).comp c) (y W (π ^ l) e.b3 e.b4 e.b6)
local notation "α" => algebraMap R T W.a₁
local notation "V" => unequalDepthSmoothOpen hπ d e hkl data hd a c

/-- Strict unequal depths with opposite uncontracted branches have smooth local outputs. -/
theorem unequalDepthSmoothOpen_opposite_mem (hk : 0 < k) (hlt : k < l) (hm : 2 * l < m)
    (p : PrimeSpectrum T) (hp : algebraMap R T π ∈ p.asIdeal) (hu : x₂ ∉ p.asIdeal)
    (hbranch : (y₁ ∈ p.asIdeal ∧ y₂ + α * x₂ ∈ p.asIdeal) ∨
      (y₁ + α * x₁ ∈ p.asIdeal ∧ y₂ ∈ p.asIdeal)) : p ∈ V := by
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
  have hlin := divided_linear_deep_mem D e (by omega : l ≤ m + 1)
  have h3 := van e.b3 (Ideal.pow_le_self (by omega) hlin.1)
  have h4 := van e.b4 (Ideal.pow_le_self (by omega) hlin.2)
  have h6 := van e.b6 (Ideal.pow_le_self (by omega)
    (divided_constant_exact_depth D e (by omega)).1)
  have hz := van (z).b3 (Ideal.pow_le_self (by
    change m + 1 - (0 + (l - k)) ≠ 0
    omega)
    (divided_linear_deep_mem D z (by omega : 0 + (l - k) ≤ m + 1)).1)
  have hu0 : ρ x₂ ≠ 0 := fun h => hu (Ideal.algebraMap_residueField_eq_zero.mp h)
  have hb : (ρ y₁ = 0 ∧ ρ y₂ = -algebraMap R K W.a₁ * ρ x₂) ∨
      (ρ y₁ = -algebraMap R K W.a₁ * ρ x₁ ∧ ρ y₂ = 0) := by
    have neg (v u : T) (h : v + α * u ∈ p.asIdeal) :
        ρ v = -algebraMap R K W.a₁ * ρ u := by
      have h0 : ρ (v + α * u) = 0 := Ideal.algebraMap_residueField_eq_zero.mpr h
      simp only [map_add, map_mul, AlgHom.commutes] at h0
      linear_combination h0
    rcases hbranch with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨Ideal.algebraMap_residueField_eq_zero.mpr h₁, neg _ _ h₂⟩
    · exact Or.inr ⟨neg _ _ h₁, Ideal.algebraMap_residueField_eq_zero.mpr h₂⟩
  have hn := unequalDepthSecantOutput_residue_vertical hπ d e hkl z (Nat.zero_add _) a c ρ
    hs ht h3 h4 h6 (van W.a₂ D.a₂_mem) (D.a₁_unit.map (algebraMap R K)).ne_zero hz hu0 hb
  apply unequalDepthSmoothOpen_mem hπ d e hkl data hd a c p
  exact fun h => hn (Ideal.algebraMap_residueField_eq_zero.mpr h)

/-- These outputs occupy an actual open in the original full supplied input scheme. -/
theorem unequalDepthDomain_opposite_image (hk : 0 < k) (hlt : k < l) (hm : 2 * l < m)
    (p : PrimeSpectrum T) (hp : algebraMap R T π ∈ p.asIdeal) (hu : x₂ ∉ p.asIdeal)
    (hbranch : (y₁ ∈ p.asIdeal ∧ y₂ + α * x₂ ∈ p.asIdeal) ∨
      (y₁ + α * x₁ ∈ p.asIdeal ∧ y₂ ∈ p.asIdeal)) :
    PrimeSpectrum.comap (algebraMap S T) p ∈ unequalDepthDomain hπ d e hkl data hd a c :=
  unequalDepthDomain_image hπ d e hkl data hd a c p
    (unequalDepthSmoothOpen_opposite_mem D d e hkl data hd a c hk hlt hm p hp hu hbranch)

/-- Opposite punctured branches in the original source are covered without a denominator premise. -/
theorem unequalDepthDomain_opposite_mem (hk : 0 < k) (hlt : k < l) (hm : 2 * l < m)
    (p : PrimeSpectrum S) (hp : algebraMap R S π ∈ p.asIdeal)
    (hx : a (x W (π ^ k) d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hu : c (x W (π ^ l) e.b3 e.b4 e.b6) ∉ p.asIdeal)
    (hbranch :
      (a (y W (π ^ k) d.b3 d.b4 d.b6) ∈ p.asIdeal ∧
        c (y W (π ^ l) e.b3 e.b4 e.b6) +
          algebraMap R S W.a₁ * c (x W (π ^ l) e.b3 e.b4 e.b6) ∈ p.asIdeal) ∨
      (a (y W (π ^ k) d.b3 d.b4 d.b6) +
          algebraMap R S W.a₁ * a (x W (π ^ k) d.b3 d.b4 d.b6) ∈ p.asIdeal ∧
        c (y W (π ^ l) e.b3 e.b4 e.b6) ∈ p.asIdeal)) :
    p ∈ unequalDepthDomain hπ d e hkl data hd a c := by
  let c₀ := unequalDepthRight hπ d e hkl c
  let dx := a (x W (π ^ k) d.b3 d.b4 d.b6) - c₀ (x W (π ^ k) d.b3 d.b4 d.b6)
  have hc₀ : c₀ (x W (π ^ k) d.b3 d.b4 d.b6) ∈ p.asIdeal := by
    rw [unequalDepthRight_x, map_pow]
    exact p.asIdeal.mul_mem_right _ (p.asIdeal.pow_mem_of_mem hp _ (by omega))
  have hdx : dx ∉ p.asIdeal := by
    intro h
    apply hx
    simpa only [dx, sub_add_cancel] using p.asIdeal.add_mem h hc₀
  obtain ⟨q, hq⟩ := (PrimeSpectrum.localization_away_comap_range T dx).ge hdx
  have memq (v : S) : algebraMap S T v ∈ q.asIdeal ↔ v ∈ p.asIdeal := by
    change v ∈ (PrimeSpectrum.comap (algebraMap S T) q).asIdeal ↔ v ∈ p.asIdeal
    rw [hq]
  have hpq : algebraMap R T π ∈ q.asIdeal := by
    rw [IsScalarTower.algebraMap_apply R S T]
    exact (memq _).mpr hp
  have huq : x₂ ∉ q.asIdeal := by
    change algebraMap S T (c (x W (π ^ l) e.b3 e.b4 e.b6)) ∉ q.asIdeal
    exact fun h => hu ((memq _).mp h)
  have hbq : (y₁ ∈ q.asIdeal ∧ y₂ + α * x₂ ∈ q.asIdeal) ∨
      (y₁ + α * x₁ ∈ q.asIdeal ∧ y₂ ∈ q.asIdeal) := by
    simpa only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
      IsScalarTower.algebraMap_apply R S T, ← map_mul, ← map_add, memq] using hbranch
  have h := unequalDepthDomain_opposite_image D d e hkl data hd a c
    hk hlt hm q hpq huq hbq
  rwa [hq] at h

end FLT.Mazur.WeierstrassDividedDepth
