/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedUnequalDepthOutput
public import FLT.Mazur.WeierstrassDividedFiniteSmoothInput
public import FLT.Mazur.WeierstrassDividedGlobalSmoothTransition

/-!
# Actual resolved smooth outputs for unequal-depth secants

Embed the constructed difference-depth output in its finite model and
restrict to its actual smooth locus. The resulting morphism promotes to
any later finite stage, with the original secant contraction unchanged.
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
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hd : l - k ≤ n)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "z" => data ⟨l - k, Nat.lt_succ_of_le hd⟩
local notation "T" => UnequalDepthSecantRing hπ d e hkl a c
local notation "o" => unequalDepthSecantOutput hπ d e hkl z (Nat.zero_add _) a c
local notation "f" => unequalDepthSecantLift hπ d e hkl z (Nat.zero_add _) a c
local notation "base" => finiteGlobalStructure hπ data (l - k) hd
local notation "U" => (base).smoothLocus
local notation "inc" => finiteSecantDividedChart hπ data (l - k) hd

/-- The actual inverse image of the difference-depth finite model's smooth locus. -/
def unequalDepthSmoothOpen : (Spec (.of T)).Opens := (f ≫ inc) ⁻¹ᵁ U

local notation "V" => unequalDepthSmoothOpen hπ d e hkl data hd a c

/-- A nonzero output derivative certifies membership at every source prime. -/
theorem unequalDepthSmoothOpen_mem (p : PrimeSpectrum T)
    (hp : o (verticalDerivative W (π ^ (0 + (l - k))) (z).b3 (z).b4 (z).b6) ∉ p.asIdeal) :
    p ∈ V := by
  let ρ : T →ₐ[R] p.asIdeal.ResidueField := IsScalarTower.toAlgHom R T _
  have hn : ((ρ).comp o)
      (verticalDerivative W (π ^ (0 + (l - k))) (z).b3 (z).b4 (z).b6) ≠ 0 :=
    fun h => hp (Ideal.algebraMap_residueField_eq_zero.mp h)
  have h := finiteDividedFieldPoint_range_smooth hπ data (l - k) hd ((ρ).comp o) hn
  have he : Spec.map (CommRingCat.ofHom ρ.toRingHom) ⟨⊥, inferInstance⟩ = p := by
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro q
    change algebraMap T p.asIdeal.ResidueField q = 0 ↔ q ∈ p.asIdeal
    exact Ideal.algebraMap_residueField_eq_zero
  have hr : Set.range (Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ f ≫ inc) ⊆ U := by
    simpa only [unequalDepthSecantLift, ← Category.assoc, ← Spec.map_comp,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp] using h
  exact hr ⟨⟨⊥, inferInstance⟩, by rw [Scheme.Hom.comp_apply, he]⟩

/-- Include the smooth-output source into the unchanged full input spectrum. -/
def unequalDepthSmoothInclusion : (V).toScheme ⟶ Spec (.of S) :=
  (V).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))

instance unequalDepthSmoothInclusion_open :
    IsOpenImmersion (unequalDepthSmoothInclusion hπ d e hkl data hd a c) := by
  let _ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap S T))) :=
    IsOpenImmersion.of_isLocalization (a (x W (π ^ k) d.b3 d.b4 d.b6) -
      unequalDepthRight hπ d e hkl c (x W (π ^ k) d.b3 d.b4 d.b6))
  unfold unequalDepthSmoothInclusion
  infer_instance

/-- The actual addition domain in the complete supplied input scheme. -/
def unequalDepthDomain : (Spec (.of S)).Opens :=
  (unequalDepthSmoothInclusion hπ d e hkl data hd a c).opensRange

local notation "O" => unequalDepthDomain hπ d e hkl data hd a c
local notation "src" => unequalDepthSmoothInclusion hπ d e hkl data hd a c

/-- Every covered secant prime maps into the actual original-source domain. -/
theorem unequalDepthDomain_image (p : PrimeSpectrum T) (hp : p ∈ V) :
    PrimeSpectrum.comap (algebraMap S T) p ∈ O :=
  ⟨⟨p, hp⟩, rfl⟩

variable (j : ℕ) (hj : j ≤ n) (hdj : l - k ≤ j)
local notation "final" => finiteGlobalStructure hπ data j hj
local notation "Uf" => (final).smoothLocus

/-- Promote the constructed smooth output to the independently chosen final stage. -/
def unequalDepthResolvedOutput : (V).toScheme ⟶ (Uf).toScheme :=
  ((f ≫ inc) ∣_ U) ≫ finiteGlobalSmoothTransition hπ data (l - k) j hdj hj

/-- The output is the actual original unequal-depth secant after contraction. -/
@[reassoc] theorem unequalDepthResolvedOutput_contraction :
    unequalDepthResolvedOutput hπ d e hkl data hd a c j hj hdj ≫
        (Uf).ι ≫ finiteGlobalContraction hπ data j hj =
      (V).ι ≫ dividedSecantToCurve W (π ^ k) d.b3 d.b4 d.b6 a
        (unequalDepthRight hπ d e hkl c) d.factor3 d.factor4 d.factor6 := by
  rw [unequalDepthResolvedOutput, Category.assoc, finiteGlobalSmoothTransition_contraction,
    morphismRestrict_ι_assoc, Category.assoc, finiteSecantDividedChart_contraction,
    unequalDepthSecantLift_contraction]
  rfl

/-- Promotion leaves the coefficient point unchanged on the entire constructed open. -/
@[reassoc] theorem unequalDepthResolvedOutput_structure :
    unequalDepthResolvedOutput hπ d e hkl data hd a c j hj hdj ≫ (Uf).ι ≫ final =
      (V).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  rw [unequalDepthResolvedOutput, Category.assoc, finiteGlobalSmoothTransition_structure,
    morphismRestrict_ι_assoc, Category.assoc, finiteSecantDividedChart_structure,
    unequalDepthSecantLift_structure]
  rfl

/-- Transport the resolved output to its genuine open in the full supplied input scheme. -/
def unequalDepthResolvedAddition : (O).toScheme ⟶ (Uf).toScheme :=
  (src).isoOpensRange.inv ≫ unequalDepthResolvedOutput hπ d e hkl data hd a c j hj hdj

/-- The image-open construction recovers the whole local output. -/
@[reassoc] theorem unequalDepthResolvedAddition_formula :
    (src).isoOpensRange.hom ≫
      unequalDepthResolvedAddition hπ d e hkl data hd a c j hj hdj =
        unequalDepthResolvedOutput hπ d e hkl data hd a c j hj hdj := by
  unfold unequalDepthResolvedAddition unequalDepthDomain
  rw [Iso.hom_inv_id_assoc]

/-- The addition on the original source keeps its coefficient point. -/
@[reassoc] theorem unequalDepthResolvedAddition_structure :
    unequalDepthResolvedAddition hπ d e hkl data hd a c j hj hdj ≫ (Uf).ι ≫ final =
      (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  apply (cancel_epi (src).isoOpensRange.hom).mp
  rw [unequalDepthResolvedAddition_formula_assoc, unequalDepthResolvedOutput_structure]
  unfold unequalDepthDomain
  rw [Scheme.Hom.isoOpensRange_hom_ι_assoc]
  simp only [unequalDepthSmoothInclusion, Category.assoc, ← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
