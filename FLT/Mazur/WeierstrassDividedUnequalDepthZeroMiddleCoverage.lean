/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedMiddleFieldSmooth

/-!
# Exact middle-depth coverage from a zero-depth input

The difference-depth output is itself at the middle depth. Its horizontal
partial is nonzero on the closed fiber, even when the vertical partial
vanishes. Only the initial input's abscissa is inverted.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
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

/-- Zero-depth secants to a middle-depth terminal point have smooth outputs. -/
theorem unequalDepthSmoothOpen_zero_middle_mem (hk : k = 0) (hl : 0 < l)
    (hm : 2 * l = m) (p : PrimeSpectrum T) (hp : algebraMap R T π ∈ p.asIdeal) :
    p ∈ V := by
  let ρ : T →ₐ[R] p.asIdeal.ResidueField := IsScalarTower.toAlgHom R T _
  have hπ0 : algebraMap R p.asIdeal.ResidueField π = 0 := by
    rw [IsScalarTower.algebraMap_apply R T p.asIdeal.ResidueField]
    exact Ideal.algebraMap_residueField_eq_zero.mpr hp
  let o := unequalDepthSecantOutput hπ d e hkl z (Nat.zero_add _) a c
  let f := unequalDepthSecantLift hπ d e hkl z (Nat.zero_add _) a c
  let inc := finiteSecantDividedChart hπ data (l - k) hd
  have h := finiteMiddleFieldPoint_range_smooth D (by omega : 0 < l - k)
    (by omega : 2 * (l - k) = m) hπ0 data hd (ρ.comp o)
  have he : Spec.map (CommRingCat.ofHom ρ.toRingHom) ⟨⊥, inferInstance⟩ = p := by
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro q
    change algebraMap T p.asIdeal.ResidueField q = 0 ↔ q ∈ p.asIdeal
    exact Ideal.algebraMap_residueField_eq_zero
  have hr : Set.range (Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ f ≫ inc) ⊆
      (finiteGlobalStructure hπ data (l - k) hd).smoothLocus := by
    simpa only [f, unequalDepthSecantLift, ← Category.assoc, ← Spec.map_comp,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp] using h
  exact hr ⟨⟨⊥, inferInstance⟩, by rw [Scheme.Hom.comp_apply, he]⟩

/-- Every punctured zero-depth input to a middle-depth terminal input is covered. -/
theorem unequalDepthDomain_zero_middle_mem (hk : k = 0) (hl : 0 < l) (hm : 2 * l = m)
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
    (unequalDepthSmoothOpen_zero_middle_mem D d e hkl data hd a c hk hl hm q hpq)
  rwa [hq] at h

/-- All shallower depths, including zero, have actual punctured middle-terminal coverage. -/
theorem unequalDepthDomain_all_middle_mem (hlt : k < l) (hm : 2 * l = m)
    (p : PrimeSpectrum S) (hp : algebraMap R S π ∈ p.asIdeal)
    (hx : a (x W (π ^ k) d.b3 d.b4 d.b6) ∉ p.asIdeal) :
    p ∈ unequalDepthDomain hπ d e hkl data hd a c := by
  by_cases hk : k = 0
  · exact unequalDepthDomain_zero_middle_mem D d e hkl data hd a c hk (by omega) hm p hp hx
  · exact unequalDepthDomain_middle_mem D d e hkl data hd a c (by omega) hlt hm p hp hx

end FLT.Mazur.WeierstrassDividedDepth
