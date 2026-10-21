/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialTerminalUnequalAddition
public import FLT.Mazur.WeierstrassDividedArithmeticAtlasPairPresentation
public import FLT.Mazur.SchemeArithmeticCoefficientSupport

/-!
# Initial/terminal outputs on the original arithmetic inputs

Pull the uncontracted unequal-depth formula back to the exact full
arithmetic chart product. At middle depth, puncturing the initial abscissa
covers every terminal input in both orders and at every arithmetic order.
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
  retainedInitialFormulaCoordinates terminalLowerCoordinates
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n)
local notation "a" => (Fin.succ ⟨j + 1, Nat.lt_succ_self (j + 1)⟩ : Fin (j + 3))
local notation "b" => (1 : Fin (j + 3))
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "e" => data ⟨j, Nat.lt_succ_of_le hj⟩
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
local notation "P" => arithmeticAtlasPairPresentation hπ data m j hj a b
local notation "F" => initialTerminalUnequalFormulaInput hπ data j hj

/-- The entire original arithmetic pair supplies the initial and full terminal coordinates. -/
def arithmeticInitialTerminalFormulaInput :
    pullback fa fb ⟶ Spec (.of (UnequalPairRing d e)) := P ≫ F

local notation "input" => arithmeticInitialTerminalFormulaInput hπ data m j hj

/-- The actual coordinate input keeps the arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticInitialTerminalFormulaInput_structure :
    input ≫ Spec.map (CommRingCat.ofHom (algebraMap R (UnequalPairRing d e))) =
      pullback.fst fa fb ≫ fa ≫ q := by
  rw [arithmeticInitialTerminalFormulaInput, Category.assoc,
    initialTerminalUnequalFormulaInput_structure,
    finiteResolvedAtlasPairInput_fst_assoc, arithmeticAtlasPairPresentation_structure]

/-- The arithmetic quotient forces closed-fiber support on every actual pair. -/
theorem arithmeticInitialTerminalFormulaInput_parameter_mem (p : (pullback fa fb : Scheme)) :
    algebraMap R (UnequalPairRing d e) π ∈ (input p).asIdeal :=
  spectrumInput_parameter_mem π m input (pullback.fst fa fb ≫ fa)
    (by simpa only [Category.assoc] using
      arithmeticInitialTerminalFormulaInput_structure hπ data m j hj) p

local notation "V" => initialTerminalUnequalOpen hπ data j hj
local notation "add" => initialTerminalUnequalAddition hπ data j hj

/-- The formula domain in the original full arithmetic pair. -/
def arithmeticInitialTerminalOpen : (pullback fa fb).Opens := P ⁻¹ᵁ V

local notation "D" => arithmeticInitialTerminalOpen hπ data m j hj

/-- Construct the smooth output with its original integral target. -/
def arithmeticInitialTerminalAddition : (D).toScheme ⟶ (U).toScheme := (P ∣_ V) ≫ add

/-- The output preserves the first original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticInitialTerminalAddition_structure :
    arithmeticInitialTerminalAddition hπ data m j hj ≫ t =
      (D).ι ≫ pullback.fst fa fb ≫ fa ≫ q := by
  rw [arithmeticInitialTerminalAddition, Category.assoc,
    initialTerminalUnequalAddition_structure, morphismRestrict_ι_assoc,
    finiteResolvedAtlasPairInput_fst_assoc, arithmeticAtlasPairPresentation_structure]
  rfl

/-- The same output preserves the original terminal arithmetic coefficient point. -/
@[reassoc] theorem arithmeticInitialTerminalAddition_structure_snd :
    arithmeticInitialTerminalAddition hπ data m j hj ≫ t =
      (D).ι ≫ pullback.snd fa fb ≫ fb ≫ q := by
  rw [arithmeticInitialTerminalAddition_structure, pullback.condition_assoc]

local notation "x₁" => unequalPairLeft d e (x W (π ^ (0 + 0)) (d).b3 (d).b4 (d).b6)

/-- No terminal puncture or vertical derivative assumption is needed at middle depth. -/
theorem arithmeticInitialTerminalOpen_middle_mem [IsLocalRing R] {depth : ℕ}
    (node : SplitNodeDepth W π depth) (hj0 : 0 < j) (hm : 2 * j = depth)
    (p : (pullback fa fb : Scheme)) (hx : x₁ ∉ (input p).asIdeal) : p ∈ D :=
  initialTerminalUnequalOpen_middle_mem hπ data j hj node hj0 hm (P p)
    (arithmeticInitialTerminalFormulaInput_parameter_mem hπ data m j hj p) hx

local notation "swap" => (pullbackSymmetry fb fa).hom

/-- Reverse the original arithmetic factors without replacing either input. -/
def arithmeticTerminalInitialOpen : (pullback fb fa).Opens := swap ⁻¹ᵁ D

local notation "E" => arithmeticTerminalInitialOpen hπ data m j hj

/-- The reverse pair has the same constructed resolved smooth output. -/
def arithmeticTerminalInitialAddition : (E).toScheme ⟶ (U).toScheme :=
  (swap ∣_ D) ≫ arithmeticInitialTerminalAddition hπ data m j hj

/-- The reversed output has the coefficient point of its terminal first factor. -/
@[reassoc] theorem arithmeticTerminalInitialAddition_structure :
    arithmeticTerminalInitialAddition hπ data m j hj ≫ t =
      (E).ι ≫ pullback.fst fb fa ≫ fb ≫ q := by
  rw [arithmeticTerminalInitialAddition, Category.assoc,
    arithmeticInitialTerminalAddition_structure_snd, morphismRestrict_ι_assoc,
    pullbackSymmetry_hom_comp_snd_assoc]
  rfl

/-- The initial second factor has the same original coefficient point. -/
@[reassoc] theorem arithmeticTerminalInitialAddition_structure_snd :
    arithmeticTerminalInitialAddition hπ data m j hj ≫ t =
      (E).ι ≫ pullback.snd fb fa ≫ fa ≫ q := by
  rw [arithmeticTerminalInitialAddition_structure, pullback.condition_assoc]

/-- Every reversed punctured initial/middle-terminal input is covered as well. -/
theorem arithmeticTerminalInitialOpen_middle_mem [IsLocalRing R] {depth : ℕ}
    (node : SplitNodeDepth W π depth) (hj0 : 0 < j) (hm : 2 * j = depth)
    (p : (pullback fb fa : Scheme)) (hx : x₁ ∉ (input (swap p)).asIdeal) : p ∈ E :=
  arithmeticInitialTerminalOpen_middle_mem hπ data m j hj node hj0 hm (swap p) hx

end FLT.Mazur.WeierstrassDividedDepth
