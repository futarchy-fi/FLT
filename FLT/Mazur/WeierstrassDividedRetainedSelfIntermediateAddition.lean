/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedSelfReciprocalAddition
public import FLT.Mazur.WeierstrassDividedAtlasPairReciprocalCoverage
public import FLT.Mazur.WeierstrassDividedAtlasPairFormulaCoverage
public import FLT.Mazur.WeierstrassDividedPreMiddlePuncturedVertical

/-!
# Punctured retained self-pairs in the intermediate depth range

The intermediate and reciprocal domains cover all punctured self-pairs,
including equal ordinates and distinct residue abscissae. The common depth
is the chart's own preceding depth, with its actual output-stage bound.
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
  atlasPairIntermediateAddition atlasPairIntermediateOpen
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
variable (hdepth : 3 * (retainedSelfFormulaDepth j a) ≤ nodeDepth)
  (hm : nodeDepth < 4 * (retainedSelfFormulaDepth j a))
 
  (hstage : (retainedSelfFormulaDepth j a) + (nodeDepth - 3 * (retainedSelfFormulaDepth j a)) ≤ j)
local notation "offset" => nodeDepth - 3 * depth
local notation "h3" => (Nat.le_trans (by omega : 3 * (0 + depth) ≤ 3 * depth) hdepth)
local notation "hrk" => ((fun (h : nodeDepth < 4 * depth) =>
  (by omega : offset ≤ 0 + depth)) hm)
local notation "hrm" => (show offset ≤ nodeDepth - 3 * (0 + depth) from by omega)
local notation "hrj" => (Nat.le_trans (by omega : (0 + depth) + offset ≤ depth + offset) hstage)
local notation "hr" => (Nat.le_trans
  (by omega : (0 + depth) + offset ≤ depth + offset) (hstage.trans hj))

include hdepth hm hstage

/-- The actual intermediate output domain in the full retained self-pair. -/
def retainedSelfIntermediateOpen : (pullback ta ta).Opens :=
  atlasPairIntermediateOpen (r := nodeDepth - 3 * depth) node
    h3 hrk hrm data hr j hj idx idx d f f hf hf

local notation "V" => retainedSelfIntermediateOpen node data j hj a hdepth hm hstage
local notation "Q" => retainedSelfReciprocalOpen hπ data j hj a

/-- Construct the intermediate output in the unchanged final smooth model. -/
def retainedSelfIntermediateAddition : (V).toScheme ⟶ (U).toScheme :=
  atlasPairIntermediateAddition (r := nodeDepth - 3 * depth) node
    h3 hrk hrm data hr j hj hrj idx idx d f f hf hf

local notation "add" => retainedSelfIntermediateAddition node data j hj a hdepth hm hstage

/-- The intermediate output preserves the first original coefficient point. -/
@[reassoc] theorem retainedSelfIntermediateAddition_structure :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj idx idx ≫
      pullback.fst t t ≫ t := by
  simpa only [Category.assoc, atlasPairIntermediateInput, retainedSelfIntermediateOpen,
    retainedSelfIntermediateAddition] using
    (atlasPairIntermediateAddition_structure (r := nodeDepth - 3 * depth) node
      h3 hrk hrm data hr j hj hrj idx idx d f f hf hf)

/-- The output preserves the second original coefficient point as well. -/
@[reassoc] theorem retainedSelfIntermediateAddition_structure_snd :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj idx idx ≫
      pullback.snd t t ≫ t := by
  rw [retainedSelfIntermediateAddition_structure, pullback.condition]

/-- No branch, ordinate, derivative, or secant-denominator premise is needed for coverage. -/
theorem retainedSelfIntermediate_or_reciprocal_mem (p : (pullback ta ta : Scheme))
    (hp : algebraMap R P π ∈ (input p).asIdeal)
    (hx : al (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6) ∉ (input p).asIdeal)
    (hu : ar (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6) ∉ (input p).asIdeal) :
    p ∈ V ∨ p ∈ Q := by
  have hk : 0 < 0 + depth := by omega
  have hpre : 2 * (0 + depth) < nodeDepth := by omega
  exact atlasPairIntermediate_or_reciprocal_mem (r := nodeDepth - 3 * depth) node
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
theorem retainedSelfIntermediateOpen_equal_mem (p : (pullback ta ta : Scheme))
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
  exact atlasPairIntermediateOpen_mem_tangent (r := nodeDepth - 3 * depth) node
    h3 hrk hrm data hr j hj idx idx
    d f f hf hf p (by omega) (by omega) hp hx he

/-- Distinct punctured residue abscissae lie in the actual secant domain. -/
theorem retainedSelfIntermediateOpen_distinct_mem (p : (pullback ta ta : Scheme))
    (hp : algebraMap R P π ∈ (input p).asIdeal)
    (hx : x₁ - x₂ ∉ (input p).asIdeal)
    (hu : x₁ ∉ (input p).asIdeal) (hv : x₂ ∉ (input p).asIdeal) : p ∈ V := by
  have hk : 0 < 0 + depth := by omega
  have hpre : 2 * (0 + depth) < nodeDepth := by omega
  exact atlasPairIntermediateOpen_mem_secant (r := nodeDepth - 3 * depth) node
    h3 hrk hrm data hr j hj idx idx
    d f f hf hf p hk (by omega) (by omega) hp
    (preMiddleInput_vertical_not_mem node d al hk hpre (input p) hp hu)
    (preMiddleInput_vertical_not_mem node d ar hk hpre (input p) hp hv) hx

end FLT.Mazur.WeierstrassDividedDepth
