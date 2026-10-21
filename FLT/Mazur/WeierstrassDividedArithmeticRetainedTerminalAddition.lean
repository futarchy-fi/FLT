/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedTerminalUnequalAddition
public import FLT.Mazur.WeierstrassDividedArithmeticAtlasPairPresentation

/-!
# Mixed retained/terminal addition at every arithmetic order

The source is the relative product of the original full smooth arithmetic
charts. The divided inputs preserve both entire integral projections, and
the constructed output has the original arithmetic coefficient point.
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
local notation "F" => retainedTerminalUnequalFormulaInput hπ data j hj k l hk hl

/-- The complete original mixed arithmetic pair supplies both divided inputs. -/
def arithmeticRetainedTerminalFormulaInput :
    pullback fa fb ⟶ Spec (.of (UnequalPairRing d e)) := P ≫ F

local notation "input" => arithmeticRetainedTerminalFormulaInput hπ data m j hj k l hk hl

/-- The first divided input is the full retained arithmetic coordinate projection. -/
@[reassoc] theorem arithmeticRetainedTerminalFormulaInput_left :
    input ≫ Spec.map (CommRingCat.ofHom (unequalPairLeft d e).toRingHom) =
      pullback.fst fa fb ≫ (O a).ι ≫ coords a ≫ f := by
  rw [arithmeticRetainedTerminalFormulaInput, Category.assoc,
    retainedTerminalUnequalFormulaInput_left]
  dsimp only [arithmeticAtlasPairPresentation]
  rw [atlasPairPresentation_first_assoc]
  rfl

/-- The second divided input retains the whole terminal arithmetic coordinate projection. -/
@[reassoc] theorem arithmeticRetainedTerminalFormulaInput_right :
    input ≫ Spec.map (CommRingCat.ofHom (unequalPairRight d e).toRingHom) =
      pullback.snd fa fb ≫ (O b).ι ≫ coords b ≫ g := by
  rw [arithmeticRetainedTerminalFormulaInput, Category.assoc,
    retainedTerminalUnequalFormulaInput_right]
  dsimp only [arithmeticAtlasPairPresentation]
  rw [atlasPairPresentation_second_assoc]
  rfl

variable (hkl : k ≤ l)
local notation "V" => retainedTerminalUnequalOpen hπ data j hj k l hk hl hkl
local notation "add" => retainedTerminalUnequalAddition hπ data j hj k l hk hl hkl

/-- The mixed output domain in the original smooth arithmetic relative product. -/
def arithmeticRetainedTerminalOpen : (pullback fa fb).Opens := P ⁻¹ᵁ V

local notation "D" => arithmeticRetainedTerminalOpen hπ data m j hj k l hk hl hkl

/-- Construct the resolved smooth output over every original arithmetic quotient. -/
def arithmeticRetainedTerminalAddition : (D).toScheme ⟶ (U).toScheme := (P ∣_ V) ≫ add

/-- The output has exactly the first input's original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticRetainedTerminalAddition_structure :
    arithmeticRetainedTerminalAddition hπ data m j hj k l hk hl hkl ≫ t =
      (D).ι ≫ pullback.fst fa fb ≫ fa ≫ q := by
  rw [arithmeticRetainedTerminalAddition, Category.assoc,
    retainedTerminalUnequalAddition_structure]
  dsimp only [retainedTerminalUnequalInput]
  simp only [Category.assoc]
  rw [morphismRestrict_ι_assoc,
    finiteResolvedAtlasPairInput_fst_assoc, arithmeticAtlasPairPresentation_structure]
  simp only [Category.assoc, arithmeticRetainedTerminalOpen]

/-- The original terminal arithmetic coefficient point is the same one. -/
@[reassoc] theorem arithmeticRetainedTerminalAddition_structure_snd :
    arithmeticRetainedTerminalAddition hπ data m j hj k l hk hl hkl ≫ t =
      (D).ι ≫ pullback.snd fa fb ≫ fb ≫ q := by
  rw [arithmeticRetainedTerminalAddition_structure, pullback.condition_assoc]

local notation "al" => unequalPairLeft d e
local notation "ar" => unequalPairRight d e
local notation "x₁" => al (x W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6)
local notation "y₁" => al (y W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6)
local notation "x₂" => ar (x W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6)
local notation "y₂" => ar (y W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6)
local notation "α" => algebraMap R (UnequalPairRing d e) W.a₁

/-- Opposite punctured mixed inputs at every arithmetic order have constructed outputs. -/
theorem arithmeticRetainedTerminalOpen_opposite_mem [IsLocalRing R] {depth : ℕ}
    (node : SplitNodeDepth W π depth) (hk0 : 0 < k) (hlt : k < l) (hm : 2 * l < depth)
    (p : (pullback fa fb : Scheme))
    (hp : algebraMap R (UnequalPairRing d e) π ∈ (input p).asIdeal)
    (hx : x₁ ∉ (input p).asIdeal) (hu : x₂ ∉ (input p).asIdeal)
    (hb : (y₁ ∈ (input p).asIdeal ∧ y₂ + α * x₂ ∈ (input p).asIdeal) ∨
      (y₁ + α * x₁ ∈ (input p).asIdeal ∧ y₂ ∈ (input p).asIdeal)) : p ∈ D :=
  retainedTerminalUnequalOpen_opposite_mem hπ data j hj k l hk hl hkl
    node hk0 hlt hm (P p) hp hx hu hb

end FLT.Mazur.WeierstrassDividedDepth
