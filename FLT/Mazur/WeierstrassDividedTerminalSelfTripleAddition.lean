/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalSelfReciprocalAddition
public import FLT.Mazur.WeierstrassDividedAtlasPairReciprocalCoverage
public import FLT.Mazur.WeierstrassDividedAtlasPairFormulaCoverage
public import FLT.Mazur.WeierstrassDividedPreMiddlePuncturedVertical

/-!
# Intermediate outputs for terminal self-pairs at triple depth

At node depth three times the terminal stage, the intermediate offset is zero.
The constructed output already lies in the supplied final model. Its union
with the reciprocal domain covers every punctured closed-fiber self-pair.
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
  atlasPairIntermediateAddition atlasPairIntermediateOpen
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n nodeDepth : ℕ}
  (node : SplitNodeDepth W π nodeDepth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (j : ℕ) (hj : j ≤ n)
local notation "hπ" => node.uniformizer_ne_zero
local notation "idx" => (1 : Fin (j + 3))
local notation "depth" => j
local notation "d" => data ⟨depth, Nat.lt_succ_of_le hj⟩
local notation "f" => terminalLowerCoordinates hπ data j hj j le_rfl
local notation "hf" => terminalLowerCoordinates_structure hπ data j hj j le_rfl
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "ta" => globalSmoothAtlasMap hπ data j hj idx ≫ t
local notation "P" => DividedPairRing W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6
local notation "input" => terminalSelfFormulaInput hπ data j hj
local notation "al" => dividedPairLeft W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6
local notation "ar" => dividedPairRight W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6
variable (hj0 : 0 < j) (hdepth : nodeDepth = 3 * j)
local notation "h3" => (show 3 * (0 + depth) ≤ nodeDepth from by omega)
local notation "hrk" => (show 0 ≤ 0 + depth from Nat.zero_le _)
local notation "hrm" => (show 0 ≤ nodeDepth - 3 * (0 + depth) from Nat.zero_le _)
local notation "hrj" => (show (0 + depth) + 0 ≤ j from by omega)
local notation "hr" => (Nat.le_trans hrj hj)

/-- The actual intermediate output domain in the full terminal self-pair. -/
def terminalSelfTripleOpen : (pullback ta ta).Opens :=
  atlasPairIntermediateOpen (r := 0) node
    h3 hrk hrm data hr j hj idx idx d f f hf hf

local notation "V" => terminalSelfTripleOpen node data j hj hdepth
local notation "Q" => terminalSelfReciprocalOpen hπ data j hj

/-- Construct the intermediate output in the unchanged final smooth model. -/
def terminalSelfTripleAddition : (V).toScheme ⟶ (U).toScheme :=
  atlasPairIntermediateAddition (r := 0) node
    h3 hrk hrm data hr j hj hrj idx idx d f f hf hf

local notation "add" => terminalSelfTripleAddition node data j hj hdepth

/-- The intermediate output preserves the first original coefficient point. -/
@[reassoc] theorem terminalSelfTripleAddition_structure :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj idx idx ≫
      pullback.fst t t ≫ t := by
  simpa only [Category.assoc, atlasPairIntermediateInput, terminalSelfTripleOpen,
    terminalSelfTripleAddition] using
    (atlasPairIntermediateAddition_structure (r := 0) node
      h3 hrk hrm data hr j hj hrj idx idx d f f hf hf)

/-- The output preserves the second original coefficient point as well. -/
@[reassoc] theorem terminalSelfTripleAddition_structure_snd :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj idx idx ≫
      pullback.snd t t ≫ t := by
  rw [terminalSelfTripleAddition_structure, pullback.condition]

include hj0

/-- No branch, ordinate, derivative, or secant-denominator premise is needed for coverage. -/
theorem terminalSelfTriple_or_reciprocal_mem (p : (pullback ta ta : Scheme))
    (hp : algebraMap R P π ∈ (input p).asIdeal)
    (hx : al (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6) ∉ (input p).asIdeal)
    (hu : ar (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6) ∉ (input p).asIdeal) :
    p ∈ V ∨ p ∈ Q := by
  have hk : 0 < 0 + depth := by omega
  have hpre : 2 * (0 + depth) < nodeDepth := by omega
  exact atlasPairIntermediate_or_reciprocal_mem (r := 0) node
    h3 hrk hrm data hr j hj idx idx
    d f f hf hf p hk (by omega) (by omega) hp
    (preMiddleInput_vertical_not_mem node d al hk hpre (input p) hp hx)
    (preMiddleInput_vertical_not_mem node d ar hk hpre (input p) hp hu)

local notation "x₁" => al (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "x₂" => ar (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "y₁" => al (y W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "y₂" => ar (y W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "E" => dividedTangentDenominator W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6 al ar

/-- Equal residue coordinates with punctured abscissa lie in the actual tangent domain. -/
theorem terminalSelfTripleOpen_equal_mem (p : (pullback ta ta : Scheme))
    (hp : algebraMap R P π ∈ (input p).asIdeal)
    (hx : x₁ - x₂ ∈ (input p).asIdeal) (hy : y₁ - y₂ ∈ (input p).asIdeal)
    (hu : x₁ ∉ (input p).asIdeal) : p ∈ V := by
  have hk : 0 < 0 + depth := by omega
  have hpre : 2 * (0 + depth) < nodeDepth := by omega
  have ha := preMiddleInput_vertical_not_mem node d al hk hpre (input p) hp hu
  have he : E ∉ (input p).asIdeal := by
    intro he
    apply ha
    have h := (input p).asIdeal.add_mem ((input p).asIdeal.add_mem he hy)
      ((input p).asIdeal.mul_mem_left (algebraMap R P W.a₁) hx)
    convert h using 1
    simp only [verticalDerivative_eq, map_add, map_mul, map_ofNat, AlgHom.commutes,
      dividedTangentDenominator]
    ring
  exact atlasPairIntermediateOpen_mem_tangent (r := 0) node
    h3 hrk hrm data hr j hj idx idx
    d f f hf hf p (by omega) (by omega) hp hx he

/-- Distinct punctured residue abscissae lie in the actual secant domain. -/
theorem terminalSelfTripleOpen_distinct_mem (p : (pullback ta ta : Scheme))
    (hp : algebraMap R P π ∈ (input p).asIdeal)
    (hx : x₁ - x₂ ∉ (input p).asIdeal)
    (hu : x₁ ∉ (input p).asIdeal) (hv : x₂ ∉ (input p).asIdeal) : p ∈ V := by
  have hk : 0 < 0 + depth := by omega
  have hpre : 2 * (0 + depth) < nodeDepth := by omega
  exact atlasPairIntermediateOpen_mem_secant (r := 0) node
    h3 hrk hrm data hr j hj idx idx
    d f f hf hf p hk (by omega) (by omega) hp
    (preMiddleInput_vertical_not_mem node d al hk hpre (input p) hp hu)
    (preMiddleInput_vertical_not_mem node d ar hk hpre (input p) hp hv) hx

end FLT.Mazur.WeierstrassDividedDepth
