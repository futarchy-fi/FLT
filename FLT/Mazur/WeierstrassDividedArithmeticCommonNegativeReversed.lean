/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticCommonNegative

/-!
# Reversed negative arithmetic retained pairs under mixed-depth bounds

Reverse the complete original arithmetic inputs, pull back the constructed
domain and output, and retain both coefficient identities. The output also
lands in the actual arithmetic base change of the final smooth model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  retainedOlderLowerCoordinates retainedOlderFormulaIndex
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n depth : ℕ} (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n) (k l : ℕ) (hk : k < j) (hl : l < j)
local notation "hπ" => node.uniformizer_ne_zero
local notation "a" => retainedOlderFormulaIndex j k hk
local notation "b" => retainedOlderFormulaIndex j l hl
local notation "d" => data ⟨k, Nat.lt_succ_of_le (hk.le.trans hj)⟩
local notation "e" => data ⟨l, Nat.lt_succ_of_le (hl.le.trans hj)⟩
local notation "f" => retainedOlderLowerCoordinates hπ data j hj k hk k le_rfl
local notation "g" => retainedOlderLowerCoordinates hπ data j hj l hl l le_rfl
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "fb" => (O b).ι ≫ chart b ≫ s
local notation "coords" => tensorIntegralAtlasProjection hπ data Q j hj
local notation "P" => arithmeticAtlasPairPresentation hπ data m j hj a b
local notation "input" => arithmeticOlderOwnFormulaInput hπ data m j hj k l hk hl
variable (hkl : k ≤ l) (hdepth : k + 2 * l ≤ depth) (hsum : k + l ≤ j) (h2 : W.a₂ = 0)
local notation "D" => arithmeticOlderCommonNegativeOpen node data m j hj k l hk hl
  hkl hdepth hsum h2
local notation "add" => arithmeticOlderCommonNegativeAddition node data m j hj k l hk hl
  hkl hdepth hsum h2
local notation "swap" => (pullbackSymmetry fb fa).hom

/-- The output domain in the full reversed arithmetic pair. -/
def arithmeticCommonNegativeReversedOpen : (pullback fb fa).Opens := swap ⁻¹ᵁ D

local notation "E" => arithmeticCommonNegativeReversedOpen node data m j hj k l hk hl
  hkl hdepth hsum h2

/-- The same constructed output on the original inputs in reverse order. -/
def arithmeticCommonNegativeReversedAddition : (E).toScheme ⟶ (U).toScheme :=
  (swap ∣_ D) ≫ add

/-- The reversed output retains its first original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticCommonNegativeReversedAddition_structure :
    arithmeticCommonNegativeReversedAddition node data m j hj k l hk hl hkl hdepth hsum h2 ≫ t =
      (E).ι ≫ pullback.fst fb fa ≫ fb ≫ q := by
  rw [arithmeticCommonNegativeReversedAddition, Category.assoc,
    arithmeticOlderCommonNegativeAddition_structure_snd, morphismRestrict_ι_assoc,
    pullbackSymmetry_hom_comp_snd_assoc]
  rfl

/-- The same output retains its second original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticCommonNegativeReversedAddition_structure_snd :
    arithmeticCommonNegativeReversedAddition node data m j hj k l hk hl hkl hdepth hsum h2 ≫ t =
      (E).ι ≫ pullback.snd fb fa ≫ fa ≫ q := by
  rw [arithmeticCommonNegativeReversedAddition_structure, pullback.condition_assoc]

/-- The reversed output is an actual morphism to the arithmetic smooth base change. -/
def arithmeticCommonNegativeReversedQuotient : (E).toScheme ⟶ pullback q t :=
  (swap ∣_ D) ≫
    arithmeticOlderCommonNegativeQuotientOutput node data m j hj k l hk hl hkl hdepth hsum h2

/-- The quotient projection has exactly the reversed first coefficient point. -/
@[reassoc] theorem arithmeticCommonNegativeReversedQuotient_base :
    arithmeticCommonNegativeReversedQuotient node data m j hj k l hk hl
        hkl hdepth hsum h2 ≫ pullback.fst q t = (E).ι ≫ pullback.fst fb fa ≫ fb := by
  rw [arithmeticCommonNegativeReversedQuotient, Category.assoc,
    arithmeticOlderCommonNegativeQuotientOutput_base, morphismRestrict_ι_assoc,
    pullback.condition, pullbackSymmetry_hom_comp_snd_assoc]
  rfl

/-- Forgetting the quotient recovers the complete reversed integral output. -/
@[reassoc] theorem arithmeticCommonNegativeReversedQuotient_integral :
    arithmeticCommonNegativeReversedQuotient node data m j hj k l hk hl
        hkl hdepth hsum h2 ≫ pullback.snd q t =
      arithmeticCommonNegativeReversedAddition node data m j hj k l hk hl hkl hdepth hsum h2 := by
  rw [arithmeticCommonNegativeReversedQuotient, Category.assoc,
    arithmeticOlderCommonNegativeQuotientOutput_integral]
  rfl

local notation "al" => unequalPairLeft d e
local notation "ar" => unequalPairRight d e
local notation "x₁" => al (x W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6)
local notation "y₁" => al (y W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6)
local notation "x₂" => ar (x W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6)
local notation "y₂" => ar (y W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6)

/-- Reversed punctured negative pairs are covered at every arithmetic order. -/
theorem arithmeticCommonNegativeReversedOpen_mem (hk0 : 0 < k) (hlt : k < l)
    (hm : 2 * (k + l) ≤ depth) (p : (pullback fb fa : Scheme))
    (hx : x₁ ∉ (input (swap p)).asIdeal) (hu : x₂ ∉ (input (swap p)).asIdeal)
    (hy : dividedTangentBranchFactor W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6 al ∈
      (input (swap p)).asIdeal)
    (hv : dividedTangentBranchFactor W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6 ar ∈
      (input (swap p)).asIdeal) : p ∈ E :=
  arithmeticOlderCommonNegativeOpen_mem node data m j hj k l hk hl hkl hdepth hsum h2
    hk0 hlt hm (swap p) hx hu hy hv

end FLT.Mazur.WeierstrassDividedDepth
