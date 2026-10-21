/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalSelfReciprocalAddition
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalSmoothPuncture
public import FLT.Mazur.WeierstrassDividedTerminalTensorProjection
public import FLT.Mazur.SchemeArithmeticCoefficientSupport
public import FLT.Mazur.WeierstrassDividedArithmeticAtlasPairPresentation

/-!
# Full arithmetic terminal self-pair coordinates and reciprocal outputs

Retain the original terminal depth in both factors. Smoothness supplies both
horizontal punctures before middle depth, over the entire arithmetic quotient.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n)
local notation "idx" => (1 : Fin (j + 3))
local notation "depth" => j
local notation "d" => data ⟨depth, Nat.lt_succ_of_le hj⟩
local notation "f" => terminalLowerCoordinates hπ data j hj j le_rfl
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj idx
local notation "fa" => (O).ι ≫ chart idx ≫ s
local notation "coords" => tensorIntegralAtlasProjection hπ data Q j hj idx
local notation "P" => arithmeticAtlasPairPresentation hπ data m j hj idx idx
local notation "F" => terminalSelfFormulaInput hπ data j hj
local notation "A" => DividedPairRing W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6

/-- Both whole original smooth arithmetic inputs supply the selected common divided coordinates. -/
def arithmeticTerminalSelfReciprocalFormulaInput : pullback fa fa ⟶ Spec (.of A) := P ≫ F

local notation "input" => arithmeticTerminalSelfReciprocalFormulaInput hπ data m j hj
local notation "al" => dividedPairLeft W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6
local notation "ar" => dividedPairRight W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6

/-- The first input preserves all functions on the original arithmetic chart. -/
@[reassoc] theorem arithmeticTerminalSelfReciprocalFormulaInput_left :
    input ≫ Spec.map (CommRingCat.ofHom (al).toRingHom) =
      pullback.fst fa fa ≫ (O).ι ≫ coords ≫ f := by
  rw [arithmeticTerminalSelfReciprocalFormulaInput, Category.assoc, terminalSelfFormulaInput,
    atlasPairFormulaInput_left]
  dsimp only [arithmeticAtlasPairPresentation]
  rw [atlasPairPresentation_first_assoc]
  rfl

/-- The second input independently preserves the entire same arithmetic chart. -/
@[reassoc] theorem arithmeticTerminalSelfReciprocalFormulaInput_right :
    input ≫ Spec.map (CommRingCat.ofHom (ar).toRingHom) =
      pullback.snd fa fa ≫ (O).ι ≫ coords ≫ f := by
  rw [arithmeticTerminalSelfReciprocalFormulaInput, Category.assoc, terminalSelfFormulaInput,
    atlasPairFormulaInput_right]
  dsimp only [arithmeticAtlasPairPresentation]
  rw [atlasPairPresentation_second_assoc]
  rfl

local notation "V" => terminalSelfReciprocalOpen hπ data j hj
local notation "add" => terminalSelfReciprocalAddition hπ data j hj

/-- The reciprocal domain in the actual full arithmetic self-pair. -/
def arithmeticTerminalSelfReciprocalOpen : (pullback fa fa).Opens := P ⁻¹ᵁ V

local notation "D" => arithmeticTerminalSelfReciprocalOpen hπ data m j hj

/-- The constructed output lies in the original final resolved smooth model. -/
def arithmeticTerminalSelfReciprocalAddition : (D).toScheme ⟶ (U).toScheme := (P ∣_ V) ≫ add

/-- The output retains exactly the first input's actual arithmetic coefficient point. -/
@[reassoc] theorem arithmeticTerminalSelfReciprocalAddition_structure :
    arithmeticTerminalSelfReciprocalAddition hπ data m j hj ≫ t =
      (D).ι ≫ pullback.fst fa fa ≫ fa ≫ q := by
  rw [arithmeticTerminalSelfReciprocalAddition, Category.assoc,
    terminalSelfReciprocalAddition_structure, morphismRestrict_ι_assoc,
    finiteResolvedAtlasPairInput_fst_assoc, arithmeticAtlasPairPresentation_structure]
  simp only [Category.assoc, arithmeticTerminalSelfReciprocalOpen]

/-- The same output retains the second original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticTerminalSelfReciprocalAddition_structure_snd :
    arithmeticTerminalSelfReciprocalAddition hπ data m j hj ≫ t =
      (D).ι ≫ pullback.snd fa fa ≫ fa ≫ q := by
  rw [arithmeticTerminalSelfReciprocalAddition_structure, pullback.condition_assoc]

local notation "x₁" => al (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "y₁" => al (y W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "x₂" => ar (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "y₂" => ar (y W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "α" => algebraMap R A W.a₁

/-- The terminal self-pair retains its complete original quotient coefficient map. -/
@[reassoc] theorem arithmeticTerminalSelfFormulaInput_structure :
    input ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      pullback.fst fa fa ≫ fa ≫ q := by
  rw [arithmeticTerminalSelfReciprocalFormulaInput, Category.assoc, terminalSelfFormulaInput,
    atlasPairFormulaInput_structure, finiteResolvedAtlasPairInput_fst_assoc,
    arithmeticAtlasPairPresentation_structure]

/-- The uniformizer vanishes at every arithmetic self-pair prime. -/
theorem arithmeticTerminalSelfFormulaInput_parameter_mem (p : (pullback fa fa : Scheme)) :
    algebraMap R A π ∈ (input p).asIdeal :=
  spectrumInput_parameter_mem π m input (pullback.fst fa fa ≫ fa)
    (by simpa only [Category.assoc] using
      arithmeticTerminalSelfFormulaInput_structure hπ data m j hj) p

local notation "E" => finiteDividedTensorAtlasIso hπ data Q j hj
local notation "tx" => tensorX W (π ^ (0 + j)) (d).b3 (d).b4 (d).b6 Q

/-- The first horizontal formula prime equals its full original tensor prime. -/
theorem arithmeticTerminalSelfFormulaInput_left_x_iff (p : (pullback fa fa : Scheme)) :
    x₁ ∈ (input p).asIdeal ↔
      tx ∈ ((E).inv ((O).ι (pullback.fst fa fa p))).asIdeal := by
  have he := arithmeticTerminalSelfReciprocalFormulaInput_left hπ data m j hj
  rw [terminalLowerCoordinates_self] at he
  change input ≫ Spec.map (CommRingCat.ofHom (al).toRingHom) =
    pullback.fst fa fa ≫ (O).ι ≫ coords ≫ 𝟙 _ at he
  rw [Category.comp_id] at he
  have hp := congrArg (fun morphism => morphism p) he
  change PrimeSpectrum.comap (al).toRingHom (input p) =
    coords ((O).ι (pullback.fst fa fa p)) at hp
  change x W (π ^ (0 + j)) (d).b3 (d).b4 (d).b6 ∈
    (PrimeSpectrum.comap (al).toRingHom (input p)).asIdeal ↔ _
  rw [hp, terminalTensorAtlasProjection_x_iff]

/-- The second horizontal formula prime equals its full original tensor prime. -/
theorem arithmeticTerminalSelfFormulaInput_right_x_iff (p : (pullback fa fa : Scheme)) :
    x₂ ∈ (input p).asIdeal ↔
      tx ∈ ((E).inv ((O).ι (pullback.snd fa fa p))).asIdeal := by
  have he := arithmeticTerminalSelfReciprocalFormulaInput_right hπ data m j hj
  rw [terminalLowerCoordinates_self] at he
  change input ≫ Spec.map (CommRingCat.ofHom (ar).toRingHom) =
    pullback.snd fa fa ≫ (O).ι ≫ coords ≫ 𝟙 _ at he
  rw [Category.comp_id] at he
  have hp := congrArg (fun morphism => morphism p) he
  change PrimeSpectrum.comap (ar).toRingHom (input p) =
    coords ((O).ι (pullback.snd fa fa p)) at hp
  change x W (π ^ (0 + j)) (d).b3 (d).b4 (d).b6 ∈
    (PrimeSpectrum.comap (ar).toRingHom (input p)).asIdeal ↔ _
  rw [hp, terminalTensorAtlasProjection_x_iff]

/-- Both full terminal inputs supply their horizontal punctures from relative smoothness. -/
theorem arithmeticTerminalSelfFormulaInput_punctured [IsLocalRing R] {nodeDepth : ℕ}
    (node : SplitNodeDepth W π nodeDepth) (hj0 : 0 < j) (hm : 2 * j < nodeDepth)
    (p : (pullback fa fa : Scheme)) :
    x₁ ∉ (input p).asIdeal ∧ x₂ ∉ (input p).asIdeal := by
  constructor
  · rw [arithmeticTerminalSelfFormulaInput_left_x_iff]
    exact arithmeticTerminalTensor_nodal_punctured hπ data m j hj node (by omega) (by omega)
      _ (pullback.fst fa fa p).property
  · rw [arithmeticTerminalSelfFormulaInput_right_x_iff]
    exact arithmeticTerminalTensor_nodal_punctured hπ data m j hj node (by omega) (by omega)
      _ (pullback.snd fa fa p).property

end FLT.Mazur.WeierstrassDividedDepth
