/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAtlasPairFormulaInput
public import FLT.Mazur.WeierstrassDividedZeroOriginalSmoothCoverage

/-!
# Smooth outputs on full resolved atlas pairs

The original-input original smooth domain pulls back to the entire relative
product of two full smooth atlas charts. Its zero-depth coverage uses only
the actual punctured inputs and their original smooth contractions.
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
local notation "O" => suppliedOriginalSmoothDomain d al ar

/-- The original smooth smooth-output open of the entire actual chart-pair product. -/
def atlasPairOriginalSmoothOpen : (pullback ta tb).Opens := input ⁻¹ᵁ O

local notation "V" => atlasPairOriginalSmoothOpen hπ data j hj a b d f g hf hg

/-- Construct the original smooth output in the full resolved smooth locus. -/
def atlasPairOriginalSmoothAddition : (V).toScheme ⟶ (U).toScheme :=
  (input ∣_ O) ≫ suppliedOriginalSmoothResolvedAddition d al ar hπ data j hj

local notation "add" => atlasPairOriginalSmoothAddition hπ data j hj a b d f g hf hg

/-- The original smooth domain embeds into the exact full resolved product. -/
def atlasPairOriginalSmoothInput : (V).toScheme ⟶ finiteResolvedProduct hπ data j hj :=
  (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b

instance atlasPairOriginalSmoothInput_open :
    IsOpenImmersion (atlasPairOriginalSmoothInput hπ data j hj a b d f g hf hg) := by
  unfold atlasPairOriginalSmoothInput
  infer_instance

/-- The constructed original smooth output retains the first input's coefficient point. -/
@[reassoc] theorem atlasPairOriginalSmoothAddition_structure :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b ≫
      pullback.fst t t ≫ t := by
  rw [atlasPairOriginalSmoothAddition, Category.assoc,
    suppliedOriginalSmoothResolvedAddition_structure, morphismRestrict_ι_assoc,
    atlasPairFormulaInput_structure]
  rfl

/-- The same output also retains the second actual input's coefficient point. -/
@[reassoc] theorem atlasPairOriginalSmoothAddition_structure_snd :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b ≫
      pullback.snd t t ≫ t := by
  rw [atlasPairOriginalSmoothAddition_structure, pullback.condition]

/-- The full original smooth output contracts to the constructed original smooth formula. -/
@[reassoc] theorem atlasPairOriginalSmoothAddition_contraction :
    add ≫ (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (input ∣_ O) ≫ suppliedOriginalSmoothAddition d al ar ≫
        (WeierstrassIntegralChart.integralSmoothOpen W).ι := by
  rw [atlasPairOriginalSmoothAddition, Category.assoc,
    suppliedOriginalSmoothResolvedAddition_contraction]

variable [IsLocalRing R] {depth : ℕ} (node : SplitNodeDepth W π depth)

include node

/-- Punctured zero-depth inputs including equal points have actual resolved outputs. -/
theorem atlasPairOriginalSmoothOpen_zero_mem (hk0 : k = 0) (hm : 0 < depth)
    (p : (pullback ta tb : Scheme))
    (hp : algebraMap R P π ∈ (input p).asIdeal)
    (hx : al (x W (π ^ k) d.b3 d.b4 d.b6) ∉ (input p).asIdeal)
    (hu : ar (x W (π ^ k) d.b3 d.b4 d.b6) ∉ (input p).asIdeal) : p ∈ V := by
  exact suppliedOriginalSmoothDomain_zeroDepth_mem node d al ar hk0 hm (input p) hp hx hu

end FLT.Mazur.WeierstrassDividedDepth
