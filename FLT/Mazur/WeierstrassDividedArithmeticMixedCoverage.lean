/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedTerminalAddition
public import FLT.Mazur.SchemeArithmeticCoefficientSupport

/-!
# Opposite mixed arithmetic inputs in both orders

The coefficient quotient forces closed-fiber support, so coverage needs no
separate uniformizer premise. Reversing the two original full arithmetic
inputs gives a constructed output with both coefficient identities intact.
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
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n) (k l : ℕ) (hk : k < j) (hl : l ≤ j)
local notation "a" => retainedOlderFormulaIndex j k hk
local notation "b" => (1 : Fin (j + 3))
local notation "d" => data ⟨k, Nat.lt_succ_of_le (hk.le.trans hj)⟩
local notation "e" => data ⟨l, Nat.lt_succ_of_le (hl.trans hj)⟩
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
local notation "input" => arithmeticRetainedTerminalFormulaInput hπ data m j hj k l hk hl

/-- Both mixed divided inputs have precisely the original arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticRetainedTerminalFormulaInput_structure :
    input ≫ Spec.map (CommRingCat.ofHom (algebraMap R (UnequalPairRing d e))) =
      pullback.fst fa fb ≫ fa ≫ q := by
  rw [arithmeticRetainedTerminalFormulaInput, Category.assoc,
    retainedTerminalUnequalFormulaInput, atlasPairUnequalFormulaInput_structure,
    finiteResolvedAtlasPairInput_fst_assoc, arithmeticAtlasPairPresentation_structure]

/-- Every arithmetic input prime contains the uniformizer, including nonreduced quotients. -/
theorem arithmeticRetainedTerminalFormulaInput_parameter_mem (p : (pullback fa fb : Scheme)) :
    algebraMap R (UnequalPairRing d e) π ∈ (input p).asIdeal :=
  spectrumInput_parameter_mem π m input (pullback.fst fa fb ≫ fa)
    (by simpa only [Category.assoc] using
      arithmeticRetainedTerminalFormulaInput_structure hπ data m j hj k l hk hl) p

variable (hkl : k ≤ l)
local notation "D" => arithmeticRetainedTerminalOpen hπ data m j hj k l hk hl hkl
local notation "add" => arithmeticRetainedTerminalAddition hπ data m j hj k l hk hl hkl
local notation "swap" => (pullbackSymmetry fb fa).hom
local notation "al" => unequalPairLeft d e
local notation "ar" => unequalPairRight d e
local notation "x₁" => al (x W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6)
local notation "y₁" => al (y W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6)
local notation "x₂" => ar (x W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6)
local notation "y₂" => ar (y W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6)
local notation "α" => algebraMap R (UnequalPairRing d e) W.a₁

/-- Mixed opposite coverage needs no supplied closed-fiber assumption at any arithmetic order. -/
theorem arithmeticMixed_opposite_mem [IsLocalRing R] {depth : ℕ}
    (node : SplitNodeDepth W π depth) (hk0 : 0 < k) (hlt : k < l) (hm : 2 * l < depth)
    (p : (pullback fa fb : Scheme))
    (hx : x₁ ∉ (input p).asIdeal) (hu : x₂ ∉ (input p).asIdeal)
    (hb : (y₁ ∈ (input p).asIdeal ∧ y₂ + α * x₂ ∈ (input p).asIdeal) ∨
      (y₁ + α * x₁ ∈ (input p).asIdeal ∧ y₂ ∈ (input p).asIdeal)) : p ∈ D :=
  arithmeticRetainedTerminalOpen_opposite_mem hπ data m j hj k l hk hl hkl node hk0 hlt hm
    p (arithmeticRetainedTerminalFormulaInput_parameter_mem hπ data m j hj k l hk hl p) hx hu hb

/-- The reversed mixed domain uses the same original full arithmetic inputs in reverse order. -/
def arithmeticTerminalRetainedOpen : (pullback fb fa).Opens := swap ⁻¹ᵁ D

local notation "E" => arithmeticTerminalRetainedOpen hπ data m j hj k l hk hl hkl

/-- The reversed input order has a constructed resolved smooth output. -/
def arithmeticTerminalRetainedAddition : (E).toScheme ⟶ (U).toScheme := (swap ∣_ D) ≫ add

/-- The reversed output preserves its first, terminal, arithmetic coefficient point. -/
@[reassoc] theorem arithmeticTerminalRetainedAddition_structure :
    arithmeticTerminalRetainedAddition hπ data m j hj k l hk hl hkl ≫ t =
      (E).ι ≫ pullback.fst fb fa ≫ fb ≫ q := by
  rw [arithmeticTerminalRetainedAddition, Category.assoc,
    arithmeticRetainedTerminalAddition_structure_snd, morphismRestrict_ι_assoc,
    pullbackSymmetry_hom_comp_snd_assoc]
  rfl

/-- The reversed output preserves its second, retained, arithmetic coefficient point as well. -/
@[reassoc] theorem arithmeticTerminalRetainedAddition_structure_snd :
    arithmeticTerminalRetainedAddition hπ data m j hj k l hk hl hkl ≫ t =
      (E).ι ≫ pullback.snd fb fa ≫ fa ≫ q := by
  rw [arithmeticTerminalRetainedAddition_structure, pullback.condition_assoc]

/-- Every reversed opposite punctured input lies in the constructed reversed output domain. -/
theorem arithmeticMixed_reversed_opposite_mem [IsLocalRing R] {depth : ℕ}
    (node : SplitNodeDepth W π depth) (hk0 : 0 < k) (hlt : k < l) (hm : 2 * l < depth)
    (p : (pullback fb fa : Scheme))
    (hx : x₁ ∉ (input (swap p)).asIdeal) (hu : x₂ ∉ (input (swap p)).asIdeal)
    (hb : (y₁ ∈ (input (swap p)).asIdeal ∧ y₂ + α * x₂ ∈ (input (swap p)).asIdeal) ∨
      (y₁ + α * x₁ ∈ (input (swap p)).asIdeal ∧ y₂ ∈ (input (swap p)).asIdeal)) : p ∈ E :=
  arithmeticMixed_opposite_mem hπ data m j hj k l hk hl hkl node hk0 hlt hm (swap p) hx hu hb

end FLT.Mazur.WeierstrassDividedDepth
