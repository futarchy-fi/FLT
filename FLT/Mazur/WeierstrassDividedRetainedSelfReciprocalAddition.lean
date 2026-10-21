/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialFormulaCoordinates
public import FLT.Mazur.WeierstrassDividedRetainedOlderCoordinates
public import FLT.Mazur.WeierstrassDividedAtlasPairReciprocalAddition
public import FLT.Mazur.WeierstrassDividedEqualBranchReciprocalCoverage

/-!
# Reciprocal outputs on equal-creation-depth retained pairs

Select the original initial chart or any retained older chart. The full
smooth self-pair has constructed reciprocal outputs, including the initial
self-pair at stage zero. No positive-depth or pre-middle bound is imposed.
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
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (j : ℕ) (hj : j ≤ n) (a : Option (Fin j))

/-- None selects the initial chart; an older chart uses its own preceding divided depth. -/
def retainedSelfFormulaDepth : ℕ := a.elim 0 Fin.val

/-- Each selected divided depth belongs to the original final-stage data. -/
theorem retainedSelfFormulaDepth_le : retainedSelfFormulaDepth j a ≤ j := by
  cases a with
  | none => exact Nat.zero_le j
  | some k => exact k.isLt.le

/-- The selected chart's actual index in the complete original atlas. -/
def retainedSelfFormulaIndex : Fin (j + 3) :=
  match a with
  | none => Fin.succ ⟨j + 1, Nat.lt_succ_self (j + 1)⟩
  | some k => retainedOlderFormulaIndex j k.val k.isLt

local notation "idx" => retainedSelfFormulaIndex j a
local notation "depth" => retainedSelfFormulaDepth j a
local notation "d" => data ⟨depth, Nat.lt_succ_of_le ((retainedSelfFormulaDepth_le j a).trans hj)⟩

/-- The entire selected integral chart supplies its own divided coordinates. -/
def retainedSelfFormulaCoordinates : globalIntegralAtlasObject data j hj idx ⟶ chart d := by
  cases a with
  | none => exact retainedInitialFormulaCoordinates data j hj
  | some k => exact retainedOlderLowerCoordinates hπ data j hj k.val k.isLt k.val le_rfl

local notation "f" => retainedSelfFormulaCoordinates hπ data j hj a

/-- The selected chart's coordinates preserve the original coefficient point. -/
@[reassoc] theorem retainedSelfFormulaCoordinates_structure :
    f ≫ Spec.map (CommRingCat.ofHom (algebraMap R
      (Coordinate W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6))) =
        globalIntegralAtlasMap hπ data j hj idx ≫ finiteGlobalStructure hπ data j hj := by
  cases a with
  | none => exact retainedInitialFormulaCoordinates_structure hπ data j hj
  | some k =>
    exact retainedOlderLowerCoordinates_structure hπ data j hj k.val k.isLt k.val le_rfl

local notation "hf" => retainedSelfFormulaCoordinates_structure hπ data j hj a
variable [IsNoetherianRing R]
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "ta" => globalSmoothAtlasMap hπ data j hj idx ≫ t
local notation "P" => DividedPairRing W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6

/-- Both full original smooth inputs retain their selected divided coordinates. -/
def retainedSelfFormulaInput : pullback ta ta ⟶ Spec (.of P) :=
  atlasPairFormulaInput hπ data j hj idx idx d f f hf hf

local notation "input" => retainedSelfFormulaInput hπ data j hj a
local notation "al" => dividedPairLeft W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6
local notation "ar" => dividedPairRight W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6

/-- The reciprocal domain of the actual full equal-creation-depth pair. -/
def retainedSelfReciprocalOpen : (pullback ta ta).Opens :=
  atlasPairReciprocalOpen hπ data j hj idx idx d f f hf hf

local notation "V" => retainedSelfReciprocalOpen hπ data j hj a

/-- Construct the reciprocal output in the unchanged final smooth model. -/
def retainedSelfReciprocalAddition : (V).toScheme ⟶ (U).toScheme :=
  atlasPairReciprocalAddition hπ data j hj idx idx d f f hf hf

local notation "add" => retainedSelfReciprocalAddition hπ data j hj a

/-- The output keeps the first original input's coefficient point. -/
@[reassoc] theorem retainedSelfReciprocalAddition_structure :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj idx idx ≫
      pullback.fst t t ≫ t :=
  atlasPairReciprocalAddition_structure hπ data j hj idx idx d f f hf hf

/-- The output keeps the second original input's coefficient point as well. -/
@[reassoc] theorem retainedSelfReciprocalAddition_structure_snd :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj idx idx ≫
      pullback.snd t t ≫ t := by
  rw [retainedSelfReciprocalAddition_structure, pullback.condition]

/-- Its original cubic contraction is precisely the constructed reciprocal formula. -/
@[reassoc] theorem retainedSelfReciprocalAddition_contraction :
    add ≫ (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (input ∣_ suppliedReciprocalDomain d al ar) ≫ suppliedReciprocalOriginalSmooth d al ar ≫
        (WeierstrassIntegralChart.integralSmoothOpen W).ι :=
  atlasPairReciprocalAddition_contraction hπ data j hj idx idx d f f hf hf

local notation "x₁" => al (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "y₁" => al (y W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "x₂" => ar (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "y₂" => ar (y W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "α" => algebraMap R P W.a₁

/-- Equal residue abscissae and different ordinates are covered at any creation depth. -/
theorem retainedSelfReciprocalOpen_mem (p : (pullback ta ta : Scheme))
    (hx : x₁ - x₂ ∈ (input p).asIdeal) (hy : y₁ - y₂ ∉ (input p).asIdeal) : p ∈ V :=
  atlasPairReciprocalOpen_mem hπ data j hj idx idx d f f hf hf p hx hy

/-- Opposite punctured equal-abscissa branches supply the required ordinate difference. -/
theorem retainedSelfReciprocalOpen_opposite_mem (hα : IsUnit W.a₁)
    (p : (pullback ta ta : Scheme)) (hx : x₁ - x₂ ∈ (input p).asIdeal)
    (hu : x₂ ∉ (input p).asIdeal)
    (hb : (y₁ ∈ (input p).asIdeal ∧ y₂ + α * x₂ ∈ (input p).asIdeal) ∨
      (y₁ + α * x₁ ∈ (input p).asIdeal ∧ y₂ ∈ (input p).asIdeal)) : p ∈ V :=
  suppliedReciprocalDomain_opposite_mem d al ar hα (input p) hx hu hb

end FLT.Mazur.WeierstrassDividedDepth
