/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalReflectedNegative

/-!
# Arithmetic reflected outputs with the full terminal factor

The original terminal input may keep its final depth. Pull back the actual
reflected output at every arithmetic order, preserving both coefficient
maps and constructing the output on the quotient base change.
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
  retainedOlderLowerCoordinates retainedOlderFormulaIndex terminalLowerCoordinates
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n depth : ℕ} (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n) (k l : ℕ) (hk : k < j) (hl : l ≤ j)
local notation "hπ" => node.uniformizer_ne_zero
local notation "a" => retainedOlderFormulaIndex j k hk
local notation "b" => (1 : Fin (j + 3))
local notation "d" => data ⟨k, Nat.lt_succ_of_le (hk.le.trans hj)⟩
local notation "e" => data ⟨l, Nat.lt_succ_of_le (hl.trans hj)⟩
local notation "f" => retainedOlderLowerCoordinates hπ data j hj k hk k le_rfl
local notation "g" => terminalLowerCoordinates hπ data j hj l hl
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
local notation "input" => arithmeticRetainedTerminalFormulaInput hπ data m j hj k l hk hl
variable (hkl : k ≤ l) (hdepth : 2 * l ≤ depth) (hnear : depth ≤ k + 2 * l)
  (hsum : depth - k - l ≤ j) (h2 : W.a₂ = 0)
local notation "D" => arithTerminalReflectedNegativeOpen node data m j hj k l hk hl
  hkl hdepth hnear hsum h2
local notation "add" => arithTerminalReflectedNegativeAddition node data m j hj k l hk hl
  hkl hdepth hnear hsum h2
local notation "swap" => (pullbackSymmetry fb fa).hom

/-- The output domain in the full reversed arithmetic pair. -/
def arithTerminalReflectedNegativeReversedOpen : (pullback fb fa).Opens := swap ⁻¹ᵁ D

local notation "E" => arithTerminalReflectedNegativeReversedOpen node data m j hj k l hk hl
  hkl hdepth hnear hsum h2

/-- The same constructed output on the original inputs in reverse order. -/
def arithTerminalReflectedNegativeReversedAddition : (E).toScheme ⟶ (U).toScheme :=
  (swap ∣_ D) ≫ add

/-- The reversed output retains its first original arithmetic coefficient point. -/
@[reassoc] theorem arithTerminalReflectedNegativeReversedAddition_structure :
    arithTerminalReflectedNegativeReversedAddition node data m j hj k l hk hl
        hkl hdepth hnear hsum h2 ≫ t =
      (E).ι ≫ pullback.fst fb fa ≫ fb ≫ q := by
  rw [arithTerminalReflectedNegativeReversedAddition, Category.assoc,
    arithTerminalReflectedNegativeAddition_structure_snd, morphismRestrict_ι_assoc,
    pullbackSymmetry_hom_comp_snd_assoc]
  rfl

/-- The same output retains its second original arithmetic coefficient point. -/
@[reassoc] theorem arithTerminalReflectedNegativeReversedAddition_structure_snd :
    arithTerminalReflectedNegativeReversedAddition node data m j hj k l hk hl
        hkl hdepth hnear hsum h2 ≫ t =
      (E).ι ≫ pullback.snd fb fa ≫ fa ≫ q := by
  rw [arithTerminalReflectedNegativeReversedAddition_structure, pullback.condition_assoc]

/-- The reversed output is an actual morphism to the arithmetic smooth base change. -/
def arithTerminalReflectedNegativeReversedQuotient : (E).toScheme ⟶ pullback q t :=
  (swap ∣_ D) ≫
    arithTerminalReflectedNegativeQuotientOutput node data m j hj k l hk hl
      hkl hdepth hnear hsum h2

/-- The quotient projection has exactly the reversed first coefficient point. -/
@[reassoc] theorem arithTerminalReflectedNegativeReversedQuotient_base :
    arithTerminalReflectedNegativeReversedQuotient node data m j hj k l hk hl
        hkl hdepth hnear hsum h2 ≫ pullback.fst q t = (E).ι ≫ pullback.fst fb fa ≫ fb := by
  rw [arithTerminalReflectedNegativeReversedQuotient, Category.assoc,
    arithTerminalReflectedNegativeQuotientOutput_base, morphismRestrict_ι_assoc,
    pullback.condition, pullbackSymmetry_hom_comp_snd_assoc]
  rfl

/-- Forgetting the quotient recovers the complete reversed integral output. -/
@[reassoc] theorem arithTerminalReflectedNegativeReversedQuotient_integral :
    arithTerminalReflectedNegativeReversedQuotient node data m j hj k l hk hl
        hkl hdepth hnear hsum h2 ≫ pullback.snd q t =
      arithTerminalReflectedNegativeReversedAddition node data m j hj k l hk hl
      hkl hdepth hnear hsum h2 := by
  rw [arithTerminalReflectedNegativeReversedQuotient, Category.assoc,
    arithTerminalReflectedNegativeQuotientOutput_integral]
  rfl

local notation "al" => unequalPairLeft d e
local notation "ar" => unequalPairRight d e
local notation "x₁" => al (x W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6)
local notation "y₁" => al (y W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6)
local notation "x₂" => ar (x W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6)
local notation "y₂" => ar (y W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6)

/-- Reversed punctured negative pairs are covered at every arithmetic order. -/
theorem arithTerminalReflectedNegativeReversedOpen_mem (hk0 : 0 < k) (hlt : k < l)
    (hm : 2 * l < depth) (p : (pullback fb fa : Scheme))
    (hx : x₁ ∉ (input (swap p)).asIdeal) (hu : x₂ ∉ (input (swap p)).asIdeal)
    (hy : dividedTangentBranchFactor W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6 al ∈
      (input (swap p)).asIdeal)
    (hv : dividedTangentBranchFactor W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6 ar ∈
      (input (swap p)).asIdeal) : p ∈ E :=
  arithTerminalReflectedNegativeOpen_mem node data m j hj k l hk hl
    hkl hdepth hnear hsum h2
    hk0 hlt hm (swap p) hx hu hy hv

/-- Reversed punctured negative pairs are covered at every order with an even terminal input. -/
theorem arithTerminalReflectedNegativeReversedOpen_terminal_mem (hk0 : 0 < k) (hlt : k < l)
    (hm : depth = 2 * l) (p : (pullback fb fa : Scheme))
    (hx : x₁ ∉ (input (swap p)).asIdeal) (hu : x₂ ∉ (input (swap p)).asIdeal)
    (hy : dividedTangentBranchFactor W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6 al ∈
      (input (swap p)).asIdeal) : p ∈ E :=
  arithTerminalReflectedNegativeOpen_terminal_mem node data m j hj k l hk hl
    hkl hdepth hnear hsum h2
    hk0 hlt hm (swap p) hx hu hy

end FLT.Mazur.WeierstrassDividedDepth
