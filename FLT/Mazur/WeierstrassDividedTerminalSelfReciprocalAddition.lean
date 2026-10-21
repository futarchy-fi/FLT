/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalLowerCoordinates
public import FLT.Mazur.WeierstrassDividedAtlasPairReciprocalAddition
public import FLT.Mazur.WeierstrassDividedEqualBranchReciprocalCoverage

/-!
# Reciprocal outputs for full terminal self-pairs

Both factors retain the terminal divided depth. The reciprocal formula has
an actual output in the final smooth model, with both coefficient maps intact.
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
  (j : ℕ) (hj : j ≤ n)

local notation "idx" => (1 : Fin (j + 3))
local notation "depth" => j
local notation "d" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "f" => terminalLowerCoordinates hπ data j hj j le_rfl
local notation "hf" => terminalLowerCoordinates_structure hπ data j hj j le_rfl
variable [IsNoetherianRing R]
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "ta" => globalSmoothAtlasMap hπ data j hj idx ≫ t
local notation "P" => DividedPairRing W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6

/-- Both full original smooth inputs retain their terminal divided coordinates. -/
def terminalSelfFormulaInput : pullback ta ta ⟶ Spec (.of P) :=
  atlasPairFormulaInput hπ data j hj idx idx d f f hf hf

local notation "input" => terminalSelfFormulaInput hπ data j hj
local notation "al" => dividedPairLeft W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6
local notation "ar" => dividedPairRight W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6

/-- The reciprocal domain of the actual full terminal self-pair. -/
def terminalSelfReciprocalOpen : (pullback ta ta).Opens :=
  atlasPairReciprocalOpen hπ data j hj idx idx d f f hf hf

local notation "V" => terminalSelfReciprocalOpen hπ data j hj

/-- Construct the reciprocal output in the unchanged final smooth model. -/
def terminalSelfReciprocalAddition : (V).toScheme ⟶ (U).toScheme :=
  atlasPairReciprocalAddition hπ data j hj idx idx d f f hf hf

local notation "add" => terminalSelfReciprocalAddition hπ data j hj

/-- The output keeps the first original input's coefficient point. -/
@[reassoc] theorem terminalSelfReciprocalAddition_structure :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj idx idx ≫
      pullback.fst t t ≫ t :=
  atlasPairReciprocalAddition_structure hπ data j hj idx idx d f f hf hf

/-- The output keeps the second original input's coefficient point as well. -/
@[reassoc] theorem terminalSelfReciprocalAddition_structure_snd :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj idx idx ≫
      pullback.snd t t ≫ t := by
  rw [terminalSelfReciprocalAddition_structure, pullback.condition]

/-- Its original cubic contraction is precisely the constructed reciprocal formula. -/
@[reassoc] theorem terminalSelfReciprocalAddition_contraction :
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
theorem terminalSelfReciprocalOpen_mem (p : (pullback ta ta : Scheme))
    (hx : x₁ - x₂ ∈ (input p).asIdeal) (hy : y₁ - y₂ ∉ (input p).asIdeal) : p ∈ V :=
  atlasPairReciprocalOpen_mem hπ data j hj idx idx d f f hf hf p hx hy

/-- Opposite punctured equal-abscissa branches supply the required ordinate difference. -/
theorem terminalSelfReciprocalOpen_opposite_mem (hα : IsUnit W.a₁)
    (p : (pullback ta ta : Scheme)) (hx : x₁ - x₂ ∈ (input p).asIdeal)
    (hu : x₂ ∉ (input p).asIdeal)
    (hb : (y₁ ∈ (input p).asIdeal ∧ y₂ + α * x₂ ∈ (input p).asIdeal) ∨
      (y₁ + α * x₁ ∈ (input p).asIdeal ∧ y₂ ∈ (input p).asIdeal)) : p ∈ V :=
  suppliedReciprocalDomain_opposite_mem d al ar hα (input p) hx hu hb

end FLT.Mazur.WeierstrassDividedDepth
