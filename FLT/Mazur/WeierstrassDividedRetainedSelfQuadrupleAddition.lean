/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedSelfReciprocalAddition
public import FLT.Mazur.WeierstrassDividedQuadruplePromotedAddition
public import FLT.Mazur.WeierstrassDividedPreMiddlePuncturedVertical

/-!
# Retained self-pairs at the exact quadruple-depth boundary

Transport the constructed quadruple-depth law from its canonical doubled
family into the original supplied final model. Together with the reciprocal
domain it covers every punctured retained self-pair, including coincident
residue coordinates, subject only to the actual doubled-output stage bound.
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
variable (hk : 0 < (retainedSelfFormulaDepth j a))
  (hquad : nodeDepth = 4 * (retainedSelfFormulaDepth j a))
  (hstage : (retainedSelfFormulaDepth j a) + (retainedSelfFormulaDepth j a) ≤ j)
local notation "hrj" => (Nat.le_trans
  (by omega : (0 + depth) + (0 + depth) ≤ depth + depth) hstage)
local notation "hr" => (Nat.le_trans hrj hj)
local notation "D" => (show SplitNodeDepth W π (4 * (0 + depth)) from by
  simpa only [Nat.zero_add] using (hquad ▸ node))
local notation "O" => nodalQuadrupleAdditionOpen D d al ar

/-- The actual quadruple-depth output domain in the full retained self-pair. -/
def retainedSelfQuadrupleOpen : (pullback ta ta).Opens := input ⁻¹ᵁ O

local notation "V" => retainedSelfQuadrupleOpen node data j hj a hquad
local notation "Q" => retainedSelfReciprocalOpen hπ data j hj a

/-- Construct the quadruple-depth output in the unchanged final smooth model. -/
def retainedSelfQuadrupleAddition : (V).toScheme ⟶ (U).toScheme :=
  (input ∣_ O) ≫ quadruplePromotedAddition D data hr d al ar j hj hrj

local notation "add" => retainedSelfQuadrupleAddition node data j hj a hquad hstage

/-- The quadruple-depth output preserves the first original coefficient point. -/
@[reassoc] theorem retainedSelfQuadrupleAddition_structure :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj idx idx ≫
      pullback.fst t t ≫ t := by
  dsimp only [retainedSelfQuadrupleAddition, retainedSelfQuadrupleOpen]
  rw [Category.assoc, quadruplePromotedAddition_structure, morphismRestrict_ι_assoc]
  dsimp only [retainedSelfFormulaInput]
  rw [atlasPairFormulaInput_structure]

/-- The output preserves the second original coefficient point as well. -/
@[reassoc] theorem retainedSelfQuadrupleAddition_structure_snd :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj idx idx ≫
      pullback.snd t t ≫ t := by
  rw [retainedSelfQuadrupleAddition_structure, pullback.condition]

local notation "dx" => al (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6) -
  ar (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "E" => dividedTangentDenominator W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6 al ar

include hk in
/-- The quadruple and reciprocal outputs cover all punctured self-pairs in this range. -/
theorem retainedSelfQuadruple_or_reciprocal_mem (p : (pullback ta ta : Scheme))
    (hp : algebraMap R P π ∈ (input p).asIdeal)
    (hx : al (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6) ∉ (input p).asIdeal)
    (hu : ar (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6) ∉ (input p).asIdeal) :
    p ∈ V ∨ p ∈ Q := by
  have hk0 : 0 < 0 + depth := by omega
  have hpre : 2 * (0 + depth) < nodeDepth := by omega
  have ha := preMiddleInput_vertical_not_mem node d al hk0 hpre (input p) hp hx
  have hb := preMiddleInput_vertical_not_mem node d ar hk0 hpre (input p) hp hu
  by_cases hd : dx ∈ (input p).asIdeal
  · by_cases he : E ∈ (input p).asIdeal
    · exact Or.inr (suppliedReciprocalDomain_mem_of_denominators d al ar (input p) hd he ha)
    · exact Or.inl (nodalQuadrupleAdditionOpen_source_tangent D d al ar (input p) hp hd he)
  · exact Or.inl (nodalQuadrupleAdditionOpen_source_secant D d al ar hk0 (input p) hp ha hb hd)

end FLT.Mazur.WeierstrassDividedDepth
