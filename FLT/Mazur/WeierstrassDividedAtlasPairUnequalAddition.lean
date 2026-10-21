/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAtlasPairFormulaInput
public import FLT.Mazur.WeierstrassDividedUnequalPair
public import FLT.Mazur.WeierstrassDividedUnequalDepthCoverage

/-!
# Unequal-depth outputs on the complete resolved atlas pairs

Retain each integral chart's own divided depth, map the exact full smooth
pair product into the unequal tensor product, and pull back the constructed
smooth output domain. No contracted-input smoothness is imposed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] globalIntegralAtlasObject globalIntegralAtlasMap
  globalSmoothAtlasOpen globalSmoothAtlasMap finiteGlobalModel finiteGlobalStructure
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n k l : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (j : ℕ) (hj : j ≤ n)
  (a b : Fin (j + 3)) (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (hdj : l - k ≤ j)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "ta" => globalSmoothAtlasMap hπ data j hj a ≫ t
local notation "tb" => globalSmoothAtlasMap hπ data j hj b ≫ t
local notation "qa" => Spec.map (CommRingCat.ofHom
  (algebraMap R (Coordinate W (π ^ k) d.b3 d.b4 d.b6)))
local notation "qb" => Spec.map (CommRingCat.ofHom
  (algebraMap R (Coordinate W (π ^ l) e.b3 e.b4 e.b6)))
variable (f : globalIntegralAtlasObject data j hj a ⟶ chart d)
  (g : globalIntegralAtlasObject data j hj b ⟶ chart e)
variable
  (hf : f ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (Coordinate W (π ^ k) d.b3 d.b4 d.b6))) =
      globalIntegralAtlasMap hπ data j hj a ≫ finiteGlobalStructure hπ data j hj)
  (hg : g ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (Coordinate W (π ^ l) e.b3 e.b4 e.b6))) =
      globalIntegralAtlasMap hπ data j hj b ≫ finiteGlobalStructure hπ data j hj)
local notation "left" => (globalSmoothAtlasOpen hπ data j hj a).ι ≫ f
local notation "right" => (globalSmoothAtlasOpen hπ data j hj b).ι ≫ g

/-- The exact full atlas pair supplies both uncontracted divided coordinate systems. -/
def atlasPairUnequalFormulaInput : pullback ta tb ⟶ Spec (.of (UnequalPairRing d e)) :=
  pullback.map ta tb qa qb left right (𝟙 _) (by
    rw [Category.comp_id, atlasPairFormula_left_structure hπ data j hj a d f hf]) (by
    rw [Category.comp_id, atlasPairFormula_right_structure hπ data j hj b e g hg]) ≫
      (unequalPairSpecIso d e).hom

local notation "input" => atlasPairUnequalFormulaInput hπ data j hj a b d e f g hf hg
local notation "al" => unequalPairLeft d e
local notation "ar" => unequalPairRight d e

/-- The first tensor coordinate is exactly the supplied first integral-chart contraction. -/
@[reassoc] theorem atlasPairUnequalFormulaInput_left :
    input ≫ Spec.map (CommRingCat.ofHom (al).toRingHom) =
      pullback.fst ta tb ≫ left := by
  rw [← unequalPairSpecIso_fst, atlasPairUnequalFormulaInput, Category.assoc,
    Iso.hom_inv_id_assoc]
  exact pullback.lift_fst _ _ _

/-- The second tensor coordinate retains the deeper input before common-depth contraction. -/
@[reassoc] theorem atlasPairUnequalFormulaInput_right :
    input ≫ Spec.map (CommRingCat.ofHom (ar).toRingHom) =
      pullback.snd ta tb ≫ right := by
  rw [← unequalPairSpecIso_snd, atlasPairUnequalFormulaInput, Category.assoc,
    Iso.hom_inv_id_assoc]
  exact pullback.lift_snd _ _ _

/-- The entire unequal-depth formula source retains the resolved pair's coefficient point. -/
@[reassoc] theorem atlasPairUnequalFormulaInput_structure :
    input ≫ Spec.map (CommRingCat.ofHom (algebraMap R (UnequalPairRing d e))) =
      finiteResolvedAtlasPairInput hπ data j hj a b ≫ pullback.fst t t ≫ t := by
  rw [← WeierstrassIntegralChart.specAlgHom_structure al,
    atlasPairUnequalFormulaInput_left_assoc, hf,
    ← globalSmoothAtlasMap_inclusion_assoc, finiteResolvedAtlasPairInput_fst_assoc]

local notation "O" => unequalDepthDomain hπ d e hkl data (hdj.trans hj) al ar

/-- The unequal-depth local-output domain inside the exact complete atlas pair. -/
def atlasPairUnequalOpen : (pullback ta tb).Opens := input ⁻¹ᵁ O

local notation "V" => atlasPairUnequalOpen hπ data j hj a b d e hkl hdj f g hf hg

/-- Construct the output in the final resolved smooth locus. -/
def atlasPairUnequalAddition : (V).toScheme ⟶ (U).toScheme :=
  (input ∣_ O) ≫ unequalDepthResolvedAddition hπ d e hkl data (hdj.trans hj) al ar j hj hdj

/-- The local domain embeds in the complete resolved relative product. -/
def atlasPairUnequalInput : (V).toScheme ⟶ finiteResolvedProduct hπ data j hj :=
  (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b

instance atlasPairUnequalInput_open :
    IsOpenImmersion (atlasPairUnequalInput hπ data j hj a b d e hkl hdj f g hf hg) := by
  unfold atlasPairUnequalInput
  infer_instance

/-- The constructed output has exactly the first input's coefficient point. -/
@[reassoc] theorem atlasPairUnequalAddition_structure :
    atlasPairUnequalAddition hπ data j hj a b d e hkl hdj f g hf hg ≫ t =
      (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b ≫ pullback.fst t t ≫ t := by
  rw [atlasPairUnequalAddition, Category.assoc, unequalDepthResolvedAddition_structure,
    morphismRestrict_ι_assoc, atlasPairUnequalFormulaInput_structure]
  rfl

/-- The same output has exactly the second input's coefficient point. -/
@[reassoc] theorem atlasPairUnequalAddition_structure_snd :
    atlasPairUnequalAddition hπ data j hj a b d e hkl hdj f g hf hg ≫ t =
      (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b ≫ pullback.snd t t ≫ t := by
  rw [atlasPairUnequalAddition_structure, pullback.condition]

local notation "x₁" => al (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "y₁" => al (y W (π ^ k) d.b3 d.b4 d.b6)
local notation "x₂" => ar (x W (π ^ l) e.b3 e.b4 e.b6)
local notation "y₂" => ar (y W (π ^ l) e.b3 e.b4 e.b6)
local notation "α" => algebraMap R (UnequalPairRing d e) W.a₁

/-- Opposite punctured branches in the actual full atlas pair have constructed smooth outputs. -/
theorem atlasPairUnequalOpen_opposite_mem [IsLocalRing R] {m : ℕ}
    (D : SplitNodeDepth W π m) (hk : 0 < k) (hlt : k < l) (hm : 2 * l < m)
    (p : (pullback ta tb : Scheme))
    (hp : algebraMap R (UnequalPairRing d e) π ∈ (input p).asIdeal)
    (hx : x₁ ∉ (input p).asIdeal) (hu : x₂ ∉ (input p).asIdeal)
    (hb : (y₁ ∈ (input p).asIdeal ∧ y₂ + α * x₂ ∈ (input p).asIdeal) ∨
      (y₁ + α * x₁ ∈ (input p).asIdeal ∧ y₂ ∈ (input p).asIdeal)) : p ∈ V :=
  unequalDepthDomain_opposite_mem D d e hkl data (hdj.trans hj) al ar
    hk hlt hm (input p) hp hx hu hb

end FLT.Mazur.WeierstrassDividedDepth
