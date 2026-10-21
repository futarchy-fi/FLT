/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSumDepthIndexedOutput
public import FLT.Mazur.WeierstrassDividedFiniteSmoothInput
public import FLT.Mazur.WeierstrassDividedGlobalSmoothTransition

/-!
# Actual resolved smooth outputs for same-branch unequal-depth secants

Embed the constructed sum-depth output in its finite model and
restrict to its actual smooth locus. The resulting morphism promotes to
any later finite stage, while retaining the original coefficient point.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k l n : ℕ}
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hd : k + l ≤ n)
  (dd : Data W π (k + k)) (ee : Data W π (l + l)) (h2 : W.a₂ = 0)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "z" => data ⟨k + l, Nat.lt_succ_of_le hd⟩
local notation "T" => SumDepthSourceRing d e a c
local notation "o" => sumDepthSourceOutputAt d e a c hπ hkl dd ee z (Nat.zero_add _) h2
local notation "f" => sumDepthSourceLiftAt d e a c hπ hkl dd ee z (Nat.zero_add _) h2
local notation "base" => finiteGlobalStructure hπ data (k + l) hd
local notation "U" => (base).smoothLocus
local notation "inc" => finiteSecantDividedChart hπ data (k + l) hd

/-- The actual inverse image of the sum-depth finite model's smooth locus. -/
def sumDepthSmoothOpen : (Spec (.of T)).Opens := (f ≫ inc) ⁻¹ᵁ U

local notation "V" => sumDepthSmoothOpen hπ d e hkl data hd dd ee h2 a c

/-- A nonzero output derivative certifies membership at every source prime. -/
theorem sumDepthSmoothOpen_mem (p : PrimeSpectrum T)
    (hp : o (verticalDerivative W (π ^ (0 + (k + l))) (z).b3 (z).b4 (z).b6) ∉ p.asIdeal) :
    p ∈ V := by
  let ρ : T →ₐ[R] p.asIdeal.ResidueField := IsScalarTower.toAlgHom R T _
  have hn : ((ρ).comp o)
      (verticalDerivative W (π ^ (0 + (k + l))) (z).b3 (z).b4 (z).b6) ≠ 0 :=
    fun h => hp (Ideal.algebraMap_residueField_eq_zero.mp h)
  have h := finiteDividedFieldPoint_range_smooth hπ data (k + l) hd ((ρ).comp o) hn
  have he : Spec.map (CommRingCat.ofHom ρ.toRingHom) ⟨⊥, inferInstance⟩ = p := by
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro q
    change algebraMap T p.asIdeal.ResidueField q = 0 ↔ q ∈ p.asIdeal
    exact Ideal.algebraMap_residueField_eq_zero
  have hr : Set.range (Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ f ≫ inc) ⊆ U := by
    simpa only [sumDepthSourceLiftAt, ← Category.assoc, ← Spec.map_comp,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp] using h
  exact hr ⟨⟨⊥, inferInstance⟩, by rw [Scheme.Hom.comp_apply, he]⟩

/-- Include the smooth-output source into the unchanged full input spectrum. -/
def sumDepthSmoothInclusion : (V).toScheme ⟶ Spec (.of S) :=
  (V).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))

instance sumDepthSmoothInclusion_open :
    IsOpenImmersion (sumDepthSmoothInclusion hπ d e hkl data hd dd ee h2 a c) := by
  change IsOpenImmersion ((V).ι ≫ sumDepthSourceInclusion d e a c)
  infer_instance

/-- The actual addition domain in the complete supplied input scheme. -/
def sumDepthDomain : (Spec (.of S)).Opens :=
  (sumDepthSmoothInclusion hπ d e hkl data hd dd ee h2 a c).opensRange

local notation "O" => sumDepthDomain hπ d e hkl data hd dd ee h2 a c
local notation "src" => sumDepthSmoothInclusion hπ d e hkl data hd dd ee h2 a c

/-- Every covered secant prime maps into the actual original-source domain. -/
theorem sumDepthDomain_image (p : PrimeSpectrum T) (hp : p ∈ V) :
    PrimeSpectrum.comap (algebraMap S T) p ∈ O :=
  ⟨⟨p, hp⟩, rfl⟩

variable (j : ℕ) (hj : j ≤ n) (hdj : k + l ≤ j)
local notation "final" => finiteGlobalStructure hπ data j hj
local notation "Uf" => (final).smoothLocus

/-- Promote the constructed smooth output to the independently chosen final stage. -/
def sumDepthResolvedOutput : (V).toScheme ⟶ (Uf).toScheme :=
  ((f ≫ inc) ∣_ U) ≫ finiteGlobalSmoothTransition hπ data (k + l) j hdj hj

/-- Promotion leaves the coefficient point unchanged on the entire constructed open. -/
@[reassoc] theorem sumDepthResolvedOutput_structure :
    sumDepthResolvedOutput hπ d e hkl data hd dd ee h2 a c j hj hdj ≫ (Uf).ι ≫ final =
      (V).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  rw [sumDepthResolvedOutput, Category.assoc, finiteGlobalSmoothTransition_structure,
    morphismRestrict_ι_assoc, Category.assoc, finiteSecantDividedChart_structure,
    sumDepthSourceLiftAt_structure]
  rfl

/-- Transport the resolved output to its genuine open in the full supplied input scheme. -/
def sumDepthResolvedAddition : (O).toScheme ⟶ (Uf).toScheme :=
  (src).isoOpensRange.inv ≫ sumDepthResolvedOutput hπ d e hkl data hd dd ee h2 a c j hj hdj

/-- The image-open construction recovers the whole local output. -/
@[reassoc] theorem sumDepthResolvedAddition_formula :
    (src).isoOpensRange.hom ≫
      sumDepthResolvedAddition hπ d e hkl data hd dd ee h2 a c j hj hdj =
        sumDepthResolvedOutput hπ d e hkl data hd dd ee h2 a c j hj hdj := by
  unfold sumDepthResolvedAddition sumDepthDomain
  rw [Iso.hom_inv_id_assoc]

/-- The addition on the original source keeps its coefficient point. -/
@[reassoc] theorem sumDepthResolvedAddition_structure :
    sumDepthResolvedAddition hπ d e hkl data hd dd ee h2 a c j hj hdj ≫ (Uf).ι ≫ final =
      (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  apply (cancel_epi (src).isoOpensRange.hom).mp
  rw [sumDepthResolvedAddition_formula_assoc, sumDepthResolvedOutput_structure]
  unfold sumDepthDomain
  rw [Scheme.Hom.isoOpensRange_hom_ι_assoc]
  simp only [sumDepthSmoothInclusion, Category.assoc, ← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
