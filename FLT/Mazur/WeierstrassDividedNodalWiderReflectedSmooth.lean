/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalWiderReflectedIndexed
public import FLT.Mazur.WeierstrassDividedFiniteSmoothInput
public import FLT.Mazur.WeierstrassDividedGlobalSmoothTransition

/-!
# Resolved smooth outputs for normalized wider reflected secants

Embed the constructed reflected-depth output in its finite model and
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
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsNoetherianRing R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k l m n : ℕ} (D : SplitNodeDepth W π m)
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hd : m - k - l ≤ n)
  (hm : k + 2 * l ≤ m) (htop : m ≤ 2 * (k + l))
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "hπ" => D.uniformizer_ne_zero
local notation "z" => data ⟨m - k - l, Nat.lt_succ_of_le hd⟩
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

local notation "o" => nodalWiderReflectedSourceOutputAt d e a c D hkl hm htop z (Nat.zero_add _)
local notation "f" => nodalWiderReflectedSourceLiftAt d e a c D hkl hm htop z (Nat.zero_add _)
local notation "base" => finiteGlobalStructure hπ data (m - k - l) hd
local notation "U" => (base).smoothLocus
local notation "inc" => finiteSecantDividedChart hπ data (m - k - l) hd

/-- The actual inverse image of the reflected-depth finite model's smooth locus. -/
def nodalWiderReflectedSmoothOpen : (Spec (.of T)).Opens := (f ≫ inc) ⁻¹ᵁ U

local notation "V" => nodalWiderReflectedSmoothOpen D d e hkl data hd hm htop a c

/-- A nonzero output derivative certifies membership at every source prime. -/
theorem nodalWiderReflectedSmoothOpen_mem (p : PrimeSpectrum T)
    (hp : o (verticalDerivative W (π ^ (0 + (m - k - l))) (z).b3 (z).b4 (z).b6) ∉ p.asIdeal) :
    p ∈ V := by
  let ρ : T →ₐ[R] p.asIdeal.ResidueField := IsScalarTower.toAlgHom R T _
  have hn : ((ρ).comp o)
      (verticalDerivative W (π ^ (0 + (m - k - l))) (z).b3 (z).b4 (z).b6) ≠ 0 :=
    fun h => hp (Ideal.algebraMap_residueField_eq_zero.mp h)
  have h := finiteDividedFieldPoint_range_smooth hπ data (m - k - l) hd ((ρ).comp o) hn
  have he : Spec.map (CommRingCat.ofHom ρ.toRingHom) ⟨⊥, inferInstance⟩ = p := by
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro q
    change algebraMap T p.asIdeal.ResidueField q = 0 ↔ q ∈ p.asIdeal
    exact Ideal.algebraMap_residueField_eq_zero
  have hr : Set.range (Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ f ≫ inc) ⊆ U := by
    simpa only [nodalWiderReflectedSourceLiftAt, ← Category.assoc, ← Spec.map_comp,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp] using h
  exact hr ⟨⟨⊥, inferInstance⟩, by rw [Scheme.Hom.comp_apply, he]⟩

/-- Include the smooth-output source into the unchanged full input spectrum. -/
def nodalWiderReflectedSmoothInclusion : (V).toScheme ⟶ Spec (.of S) :=
  (V).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))

instance nodalWiderReflectedSmoothInclusion_open :
    IsOpenImmersion (nodalWiderReflectedSmoothInclusion D d e hkl data hd hm htop a c) := by
  change IsOpenImmersion ((V).ι ≫ sumDepthSourceInclusion sd se a' c')
  infer_instance

/-- The actual addition domain in the complete supplied input scheme. -/
def nodalWiderReflectedDomain : (Spec (.of S)).Opens :=
  (nodalWiderReflectedSmoothInclusion D d e hkl data hd hm htop a c).opensRange

local notation "O" => nodalWiderReflectedDomain D d e hkl data hd hm htop a c
local notation "src" => nodalWiderReflectedSmoothInclusion D d e hkl data hd hm htop a c

/-- Every covered secant prime maps into the actual original-source domain. -/
theorem nodalWiderReflectedDomain_image (p : PrimeSpectrum T) (hp : p ∈ V) :
    PrimeSpectrum.comap (algebraMap S T) p ∈ O :=
  ⟨⟨p, hp⟩, rfl⟩

variable (j : ℕ) (hj : j ≤ n) (hdj : m - k - l ≤ j)
local notation "final" => finiteGlobalStructure hπ data j hj
local notation "Uf" => (final).smoothLocus

/-- Promote the constructed smooth output to the independently chosen final stage. -/
def nodalWiderReflectedResolvedOutput : (V).toScheme ⟶ (Uf).toScheme :=
  ((f ≫ inc) ∣_ U) ≫ finiteGlobalSmoothTransition hπ data (m - k - l) j hdj hj

/-- Promotion leaves the coefficient point unchanged on the entire constructed open. -/
@[reassoc] theorem nodalWiderReflectedResolvedOutput_structure :
    nodalWiderReflectedResolvedOutput D d e hkl data hd hm htop a c j hj hdj ≫ (Uf).ι ≫ final =
      (V).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  rw [nodalWiderReflectedResolvedOutput, Category.assoc, finiteGlobalSmoothTransition_structure,
    morphismRestrict_ι_assoc, Category.assoc, finiteSecantDividedChart_structure,
    nodalWiderReflectedSourceLiftAt_structure]
  rfl

/-- Transport the resolved output to its genuine open in the full supplied input scheme. -/
def nodalWiderReflectedResolvedAddition : (O).toScheme ⟶ (Uf).toScheme :=
  (src).isoOpensRange.inv ≫ nodalWiderReflectedResolvedOutput D d e hkl data hd hm htop a c j hj hdj

/-- The image-open construction recovers the whole local output. -/
@[reassoc] theorem nodalWiderReflectedResolvedAddition_formula :
    (src).isoOpensRange.hom ≫
      nodalWiderReflectedResolvedAddition D d e hkl data hd hm htop a c j hj hdj =
        nodalWiderReflectedResolvedOutput D d e hkl data hd hm htop a c j hj hdj := by
  unfold nodalWiderReflectedResolvedAddition nodalWiderReflectedDomain
  rw [Iso.hom_inv_id_assoc]

/-- The addition on the original source keeps its coefficient point. -/
@[reassoc] theorem nodalWiderReflectedResolvedAddition_structure :
    nodalWiderReflectedResolvedAddition D d e hkl data hd hm htop a c j hj hdj ≫ (Uf).ι ≫ final =
      (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  apply (cancel_epi (src).isoOpensRange.hom).mp
  rw [nodalWiderReflectedResolvedAddition_formula_assoc,
    nodalWiderReflectedResolvedOutput_structure]
  unfold nodalWiderReflectedDomain
  rw [Scheme.Hom.isoOpensRange_hom_ι_assoc]
  simp only [nodalWiderReflectedSmoothInclusion, Category.assoc, ← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
