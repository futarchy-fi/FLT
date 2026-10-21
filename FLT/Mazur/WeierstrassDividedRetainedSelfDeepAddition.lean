/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedSelfReciprocalAddition
public import FLT.Mazur.WeierstrassDividedDeepPromotedAddition
public import FLT.Mazur.WeierstrassDividedPreMiddlePuncturedVertical

/-!
# Punctured retained self-pairs in the deep depth range

The deep and reciprocal domains cover all punctured self-pairs,
including equal ordinates and distinct residue abscissae. The common depth
is the chart's own preceding depth, and the actual output is promoted to the final smooth model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  retainedSelfFormulaCoordinates retainedSelfFormulaIndex
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n nodeDepth : ℕ}
  (node : SplitNodeDepth W π nodeDepth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (j : ℕ) (hj : j ≤ n) (a : Option (Fin j))
local notation "hπ" => node.uniformizer_ne_zero
local notation "idx" => retainedSelfFormulaIndex j a
local notation "depth" => retainedSelfFormulaDepth j a
local notation "d" => data ⟨depth, Nat.lt_succ_of_le ((retainedSelfFormulaDepth_le j a).trans hj)⟩
local notation "f" => retainedSelfFormulaCoordinates hπ data j hj a
local notation "hf" => retainedSelfFormulaCoordinates_structure hπ data j hj a
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "ta" => globalSmoothAtlasMap hπ data j hj idx ≫ t
local notation "P" => DividedPairRing W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6
local notation "input" => retainedSelfFormulaInput hπ data j hj a
local notation "al" => dividedPairLeft W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6
local notation "ar" => dividedPairRight W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6
variable (hk : 0 < (retainedSelfFormulaDepth j a))
  (hdeep : 4 * (retainedSelfFormulaDepth j a) < nodeDepth)
  (hstage : (retainedSelfFormulaDepth j a) + (retainedSelfFormulaDepth j a) ≤ j)
local notation "hrj" => (Nat.le_trans
  (by omega : (0 + depth) + (0 + depth) ≤ depth + depth) hstage)
local notation "hr" => (Nat.le_trans hrj hj)
local notation "O" => nodalDeepAdditionOpen node data hr d al ar

/-- The actual deep output domain in the full retained self-pair. -/
def retainedSelfDeepOpen : (pullback ta ta).Opens := input ⁻¹ᵁ O

local notation "V" => retainedSelfDeepOpen node data j hj a hstage
local notation "Q" => retainedSelfReciprocalOpen hπ data j hj a

/-- Construct the deep output in the unchanged final smooth model. -/
def retainedSelfDeepAddition : (V).toScheme ⟶ (U).toScheme :=
  (input ∣_ O) ≫ deepPromotedAddition node data hr d al ar j hj hrj

local notation "add" => retainedSelfDeepAddition node data j hj a hstage

/-- The deep output preserves the first original coefficient point. -/
@[reassoc] theorem retainedSelfDeepAddition_structure :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj idx idx ≫
      pullback.fst t t ≫ t := by
  dsimp only [retainedSelfDeepAddition, retainedSelfDeepOpen]
  rw [Category.assoc, deepPromotedAddition_structure, morphismRestrict_ι_assoc]
  dsimp only [retainedSelfFormulaInput]
  rw [atlasPairFormulaInput_structure]

/-- The output preserves the second original coefficient point as well. -/
@[reassoc] theorem retainedSelfDeepAddition_structure_snd :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj idx idx ≫
      pullback.snd t t ≫ t := by
  rw [retainedSelfDeepAddition_structure, pullback.condition]

local notation "dx" => al (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6) -
  ar (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "E" => dividedTangentDenominator W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6 al ar

include hk hdeep in
/-- The deep and reciprocal outputs cover all punctured self-pairs in this range. -/
theorem retainedSelfDeep_or_reciprocal_mem (p : (pullback ta ta : Scheme))
    (hp : algebraMap R P π ∈ (input p).asIdeal)
    (hx : al (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6) ∉ (input p).asIdeal)
    (hu : ar (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6) ∉ (input p).asIdeal) :
    p ∈ V ∨ p ∈ Q := by
  have hk0 : 0 < 0 + depth := by omega
  have hpre : 2 * (0 + depth) < nodeDepth := by omega
  have ha := preMiddleInput_vertical_not_mem node d al hk0 hpre (input p) hp hx
  have hb := preMiddleInput_vertical_not_mem node d ar hk0 hpre (input p) hp hu
  by_cases hd : dx ∈ (input p).asIdeal
  · by_cases he : E ∈ (input p).asIdeal
    · exact Or.inr (suppliedReciprocalDomain_mem_of_denominators d al ar (input p) hd he ha)
    · exact Or.inl (nodalDeepAdditionOpen_source_tangent node data hr d al ar
        hk0 (by omega) (input p) hp hd he)
  · exact Or.inl (nodalDeepAdditionOpen_source_secant node data hr d al ar
      hk0 (by omega) (input p) hp ha hb hd)

end FLT.Mazur.WeierstrassDividedDepth
