/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedUnequalDepthMiddleResidue
public import FLT.Mazur.WeierstrassDividedPreMiddleBranchDichotomy
public import FLT.Mazur.WeierstrassDividedUnequalDepthSmoothOutput
public import FLT.Mazur.WeierstrassDividedExactCoefficientDepth

/-!
# Coverage with an exact middle-depth terminal input

The original node depth makes the terminal constant a unit. Every punctured
shallower input then has a constructed smooth difference-depth output,
without a terminal puncture, opposite-branch, or sum-depth assumption.
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

include D in
omit [IsBezout R] [IsNoetherianRing R] in
/-- The terminal constant is a unit at the exact middle node depth. -/
theorem unequalDepthMiddle_constant_unit (hm : 2 * l = m) : IsUnit e.b6 := by
  have h := (divided_constant_exact_depth D e (by omega)).2
  have hpow : m - 2 * l + 1 = 1 := by omega
  rw [hpow, pow_one] at h
  simpa only [mem_maximalIdeal, mem_nonunits_iff, not_not] using h

/-- Every localized secant to a middle-depth terminal input has a smooth output. -/
theorem unequalDepthSmoothOpen_middle_mem (hk : 0 < k) (hlt : k < l) (hm : 2 * l = m)
    (p : PrimeSpectrum T) (hp : algebraMap R T π ∈ p.asIdeal) : p ∈ V := by
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
  have h6 := ((unequalDepthMiddle_constant_unit D e hm).map (algebraMap R K)).ne_zero
  have hz := van (z).b3 (Ideal.pow_le_self (by
    change m + 1 - (0 + (l - k)) ≠ 0
    omega)
    (divided_linear_deep_mem D z (by omega : 0 + (l - k) ≤ m + 1)).1)
  have hb : ρ y₁ = 0 ∨ ρ y₁ = -algebraMap R K W.a₁ * ρ x₁ := by
    rcases preMiddleInput_branch_dichotomy D d ((j).comp a) hk (by omega) p hp with hy | hy
    · exact Or.inl (Ideal.algebraMap_residueField_eq_zero.mpr hy)
    · have h3d := preMiddleInput_b3_mem D d (by omega) p hp
      have hn : y₁ + α * x₁ ∈ p.asIdeal := by
        simpa only [dividedTangentBranchFactor, add_sub_cancel_right] using
          p.asIdeal.sub_mem hy h3d
      have h0 : ρ (y₁ + α * x₁) = 0 := Ideal.algebraMap_residueField_eq_zero.mpr hn
      simp only [map_add, map_mul, AlgHom.commutes] at h0
      right
      linear_combination h0
  have hn := unequalDepthSecantOutput_middle_vertical hπ d e hkl z (Nat.zero_add _) a c ρ
    hs ht h3 h4 (van W.a₂ D.a₂_mem) (D.a₁_unit.map (algebraMap R K)).ne_zero hz h6 hb
  apply unequalDepthSmoothOpen_mem hπ d e hkl data hd a c p
  exact fun h => hn (Ideal.algebraMap_residueField_eq_zero.mpr h)

/-- Every punctured shallow input to a middle-depth terminal input lies in the actual domain. -/
theorem unequalDepthDomain_middle_mem (hk : 0 < k) (hlt : k < l) (hm : 2 * l = m)
    (p : PrimeSpectrum S) (hp : algebraMap R S π ∈ p.asIdeal)
    (hx : a (x W (π ^ k) d.b3 d.b4 d.b6) ∉ p.asIdeal) :
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
  have h := unequalDepthDomain_image hπ d e hkl data hd a c q
    (unequalDepthSmoothOpen_middle_mem D d e hkl data hd a c hk hlt hm q hpq)
  rwa [hq] at h

end FLT.Mazur.WeierstrassDividedDepth
