/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedSelfSmoothTangentAddition
public import FLT.Mazur.WeierstrassDividedArithmeticSelfIntermediateAddition

/-!
# Actual arithmetic zero-depth tangent coverage

The new smooth output keeps both original arithmetic coefficient maps, at
every quotient order. Coverage includes the initial and zero-created self-pairs.
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
  retainedSelfFormulaCoordinates retainedSelfFormulaIndex
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {nodeDepth n : ℕ}
  (node : SplitNodeDepth W π nodeDepth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n) (a : Option (Fin j))
local notation "hπ" => node.uniformizer_ne_zero
local notation "idx" => retainedSelfFormulaIndex j a
local notation "depth" => retainedSelfFormulaDepth j a
local notation "d" => data ⟨depth, Nat.lt_succ_of_le ((retainedSelfFormulaDepth_le j a).trans hj)⟩
local notation "f" => retainedSelfFormulaCoordinates hπ data j hj a
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
local notation "F" => retainedSelfFormulaInput hπ data j hj a
local notation "A" => DividedPairRing W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6

local notation "input" => arithmeticSelfReciprocalFormulaInput hπ data m j hj a
local notation "al" => dividedPairLeft W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6
local notation "ar" => dividedPairRight W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6

local notation "V" => retainedSelfSmoothTangentOpen hπ data j hj a
local notation "add" => retainedSelfSmoothTangentAddition hπ data j hj a

/-- The smooth tangent domain in the actual full arithmetic self-pair. -/
def arithmeticSelfSmoothTangentOpen : (pullback fa fa).Opens := P ⁻¹ᵁ V

local notation "D" => arithmeticSelfSmoothTangentOpen node data m j hj a

/-- The constructed output lies in the original final resolved smooth model. -/
def arithmeticSelfSmoothTangentAddition : (D).toScheme ⟶ (U).toScheme := (P ∣_ V) ≫ add

/-- The output retains exactly the first input's actual arithmetic coefficient point. -/
@[reassoc] theorem arithmeticSelfSmoothTangentAddition_structure :
    arithmeticSelfSmoothTangentAddition node data m j hj a ≫ t =
      (D).ι ≫ pullback.fst fa fa ≫ fa ≫ q := by
  rw [arithmeticSelfSmoothTangentAddition, Category.assoc,
    retainedSelfSmoothTangentAddition_structure, morphismRestrict_ι_assoc,
    finiteResolvedAtlasPairInput_fst_assoc, arithmeticAtlasPairPresentation_structure]
  simp only [Category.assoc, arithmeticSelfSmoothTangentOpen]

/-- The same output retains the second original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticSelfSmoothTangentAddition_structure_snd :
    arithmeticSelfSmoothTangentAddition node data m j hj a ≫ t =
      (D).ι ≫ pullback.snd fa fa ≫ fa ≫ q := by
  rw [arithmeticSelfSmoothTangentAddition_structure, pullback.condition_assoc]

local notation "x₁" => al (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "y₁" => al (y W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "x₂" => ar (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "y₂" => ar (y W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "α" => algebraMap R A W.a₁

include node

/-- Every arithmetic order covers nonzero tangent denominator at creation depth zero. -/
theorem arithmeticSelfSmoothTangentOpen_zero_mem (hz : depth = 0) (hm : 0 < nodeDepth)
    (p : (pullback fa fa : Scheme))
    (hx : x₁ ∉ (input p).asIdeal) (hu : x₂ ∉ (input p).asIdeal)
    (hd : dividedTangentDenominator W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6 al ar ∉
      (input p).asIdeal) : p ∈ D :=
  retainedSelfSmoothTangentOpen_zero_mem hπ data j hj a node hz hm (P p)
    (arithmeticSelfFormulaInput_parameter_mem node data m j hj a p) hx hu hd

end FLT.Mazur.WeierstrassDividedDepth
