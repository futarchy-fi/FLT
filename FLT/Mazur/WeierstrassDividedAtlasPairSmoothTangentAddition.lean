/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAtlasPairFormulaInput
public import FLT.Mazur.WeierstrassDividedZeroIndexedTangentCoverage

/-!
# Smooth tangent outputs on full resolved atlas pairs

The original-input smooth tangent domain pulls back to the entire relative
product of two full smooth atlas charts. Its zero-depth coverage uses only
the actual punctured inputs and their nonzero tangent denominators.
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
local notation "O" => suppliedSmoothTangentDomain d al ar

/-- The smooth tangent smooth-output open of the entire actual chart-pair product. -/
def atlasPairSmoothTangentOpen : (pullback ta tb).Opens := input ⁻¹ᵁ O

local notation "V" => atlasPairSmoothTangentOpen hπ data j hj a b d f g hf hg

/-- Construct the smooth tangent output in the full resolved smooth locus. -/
def atlasPairSmoothTangentAddition : (V).toScheme ⟶ (U).toScheme :=
  (input ∣_ O) ≫ suppliedSmoothTangentResolvedAddition d al ar hπ data j hj

local notation "add" => atlasPairSmoothTangentAddition hπ data j hj a b d f g hf hg

/-- The smooth tangent domain embeds into the exact full resolved product. -/
def atlasPairSmoothTangentInput : (V).toScheme ⟶ finiteResolvedProduct hπ data j hj :=
  (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b

instance atlasPairSmoothTangentInput_open :
    IsOpenImmersion (atlasPairSmoothTangentInput hπ data j hj a b d f g hf hg) := by
  unfold atlasPairSmoothTangentInput
  infer_instance

/-- The constructed smooth tangent output retains the first input's coefficient point. -/
@[reassoc] theorem atlasPairSmoothTangentAddition_structure :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b ≫
      pullback.fst t t ≫ t := by
  rw [atlasPairSmoothTangentAddition, Category.assoc,
    suppliedSmoothTangentResolvedAddition_structure, morphismRestrict_ι_assoc,
    atlasPairFormulaInput_structure]
  rfl

/-- The same output also retains the second actual input's coefficient point. -/
@[reassoc] theorem atlasPairSmoothTangentAddition_structure_snd :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b ≫
      pullback.snd t t ≫ t := by
  rw [atlasPairSmoothTangentAddition_structure, pullback.condition]

/-- The full smooth tangent output contracts to the constructed original smooth formula. -/
@[reassoc] theorem atlasPairSmoothTangentAddition_contraction :
    add ≫ (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (input ∣_ O) ≫ suppliedSmoothTangentOriginalSmooth d al ar ≫
        (WeierstrassIntegralChart.integralSmoothOpen W).ι := by
  rw [atlasPairSmoothTangentAddition, Category.assoc,
    suppliedSmoothTangentResolvedAddition_contraction]

variable [IsLocalRing R] {depth : ℕ} (node : SplitNodeDepth W π depth)

include node

/-- A nonzero tangent denominator gives a resolved output for punctured zero-depth pairs. -/
theorem atlasPairSmoothTangentOpen_zero_mem (hk0 : k = 0) (hm : 0 < depth)
    (p : (pullback ta tb : Scheme))
    (hp : algebraMap R P π ∈ (input p).asIdeal)
    (hx : al (x W (π ^ k) d.b3 d.b4 d.b6) ∉ (input p).asIdeal)
    (hu : ar (x W (π ^ k) d.b3 d.b4 d.b6) ∉ (input p).asIdeal)
    (hd : dividedTangentDenominator W (π ^ k) d.b3 d.b4 d.b6 al ar ∉
      (input p).asIdeal) : p ∈ V := by
  exact suppliedSmoothTangentDomain_zeroDepth_mem node d al ar hk0 hm (input p) hp hx hu hd

end FLT.Mazur.WeierstrassDividedDepth
