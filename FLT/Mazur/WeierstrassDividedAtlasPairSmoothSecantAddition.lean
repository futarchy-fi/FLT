/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAtlasPairFormulaInput
public import FLT.Mazur.WeierstrassDividedZeroIndexedSecantCoverage

/-!
# Smooth secant outputs on full resolved atlas pairs

The original-input smooth secant domain pulls back to the entire relative
product of two full smooth atlas charts. Its zero-depth coverage uses only
the actual punctured inputs and their distinct residue abscissas.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] globalIntegralAtlasObject globalIntegralAtlasMap
  globalSmoothAtlasOpen globalSmoothAtlasMap
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n k : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (a b : Fin (j + 3)) (d : Data W π k)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "ca" => globalSmoothAtlasMap hπ data j hj a
local notation "cb" => globalSmoothAtlasMap hπ data j hj b
local notation "ta" => ca ≫ t
local notation "tb" => cb ≫ t
local notation "A" => Coordinate W (π ^ k) d.b3 d.b4 d.b6
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R A))
local notation "P" => DividedPairRing W (π ^ k) d.b3 d.b4 d.b6
variable (f : globalIntegralAtlasObject data j hj a ⟶ chart d)
  (g : globalIntegralAtlasObject data j hj b ⟶ chart d)
variable
  (hf : f ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (Coordinate W (π ^ k) d.b3 d.b4 d.b6))) =
      globalIntegralAtlasMap hπ data j hj a ≫ finiteGlobalStructure hπ data j hj)
  (hg : g ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (Coordinate W (π ^ k) d.b3 d.b4 d.b6))) =
      globalIntegralAtlasMap hπ data j hj b ≫ finiteGlobalStructure hπ data j hj)
local notation "left" => (globalSmoothAtlasOpen hπ data j hj a).ι ≫ f
local notation "right" => (globalSmoothAtlasOpen hπ data j hj b).ι ≫ g

local notation "input" => atlasPairFormulaInput hπ data j hj a b d f g hf hg
local notation "al" => dividedPairLeft W (π ^ k) d.b3 d.b4 d.b6
local notation "ar" => dividedPairRight W (π ^ k) d.b3 d.b4 d.b6
local notation "O" => suppliedSmoothSecantDomain d al ar

/-- The smooth secant smooth-output open of the entire actual chart-pair product. -/
def atlasPairSmoothSecantOpen : (pullback ta tb).Opens := input ⁻¹ᵁ O

local notation "V" => atlasPairSmoothSecantOpen hπ data j hj a b d f g hf hg

/-- Construct the smooth secant output in the full resolved smooth locus. -/
def atlasPairSmoothSecantAddition : (V).toScheme ⟶ (U).toScheme :=
  (input ∣_ O) ≫ suppliedSmoothSecantResolvedAddition d al ar hπ data j hj

local notation "add" => atlasPairSmoothSecantAddition hπ data j hj a b d f g hf hg

/-- The smooth secant domain embeds into the exact full resolved product. -/
def atlasPairSmoothSecantInput : (V).toScheme ⟶ finiteResolvedProduct hπ data j hj :=
  (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b

instance atlasPairSmoothSecantInput_open :
    IsOpenImmersion (atlasPairSmoothSecantInput hπ data j hj a b d f g hf hg) := by
  unfold atlasPairSmoothSecantInput
  infer_instance

/-- The constructed smooth secant output retains the first input's coefficient point. -/
@[reassoc] theorem atlasPairSmoothSecantAddition_structure :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b ≫
      pullback.fst t t ≫ t := by
  rw [atlasPairSmoothSecantAddition, Category.assoc,
    suppliedSmoothSecantResolvedAddition_structure, morphismRestrict_ι_assoc,
    atlasPairFormulaInput_structure]
  rfl

/-- The same output also retains the second actual input's coefficient point. -/
@[reassoc] theorem atlasPairSmoothSecantAddition_structure_snd :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b ≫
      pullback.snd t t ≫ t := by
  rw [atlasPairSmoothSecantAddition_structure, pullback.condition]

/-- The full smooth secant output contracts to the constructed original smooth formula. -/
@[reassoc] theorem atlasPairSmoothSecantAddition_contraction :
    add ≫ (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (input ∣_ O) ≫ suppliedSmoothSecantOriginalSmooth d al ar ≫
        (WeierstrassIntegralChart.integralSmoothOpen W).ι := by
  rw [atlasPairSmoothSecantAddition, Category.assoc,
    suppliedSmoothSecantResolvedAddition_contraction]

variable [IsLocalRing R] {depth : ℕ} (node : SplitNodeDepth W π depth)

include node

/-- Punctured zero-depth inputs with distinct abscissas have actual resolved secant outputs. -/
theorem atlasPairSmoothSecantOpen_zero_mem (hk0 : k = 0) (hm : 0 < depth)
    (p : (pullback ta tb : Scheme))
    (hp : algebraMap R P π ∈ (input p).asIdeal)
    (hx : al (x W (π ^ k) d.b3 d.b4 d.b6) ∉ (input p).asIdeal)
    (hu : ar (x W (π ^ k) d.b3 d.b4 d.b6) ∉ (input p).asIdeal)
    (hd : al (x W (π ^ k) d.b3 d.b4 d.b6) - ar (x W (π ^ k) d.b3 d.b4 d.b6) ∉
      (input p).asIdeal) : p ∈ V := by
  exact suppliedSmoothSecantDomain_zeroDepth_mem node d al ar hk0 hm (input p) hp hx hu hd

end FLT.Mazur.WeierstrassDividedDepth
