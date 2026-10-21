/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticSelfIntermediateAddition
public import FLT.Mazur.WeierstrassDividedRetainedSelfQuadrupleAddition

/-!
# Arithmetic self-pair coverage at exact quadruple depth

The promoted quadruple-depth output and the reciprocal output cover the
entire punctured retained self-pair at every arithmetic order. The output
uses the actual supplied final model and the explicit doubled-stage bound.
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
  {W : WeierstrassCurve R} {π : R} {n nodeDepth : ℕ}
  (node : SplitNodeDepth W π nodeDepth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n) (a : Option (Fin j))
local notation "hπ" => node.uniformizer_ne_zero
local notation "idx" => retainedSelfFormulaIndex j a
local notation "depth" => retainedSelfFormulaDepth j a
local notation "d" => data ⟨depth, Nat.lt_succ_of_le ((retainedSelfFormulaDepth_le j a).trans hj)⟩
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj idx
local notation "fa" => (O).ι ≫ chart idx ≫ s
local notation "P" => arithmeticAtlasPairPresentation hπ data m j hj idx idx
local notation "A" => DividedPairRing W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6

local notation "input" => arithmeticSelfReciprocalFormulaInput hπ data m j hj a
local notation "al" => dividedPairLeft W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6
local notation "ar" => dividedPairRight W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6

local notation "E" => arithmeticSelfReciprocalOpen hπ data m j hj a

section Quadruple
variable (hquad : nodeDepth = 4 * (retainedSelfFormulaDepth j a))
  (hstage : (retainedSelfFormulaDepth j a) + (retainedSelfFormulaDepth j a) ≤ j)
local notation "V" => retainedSelfQuadrupleOpen node data j hj a hquad
local notation "add" => retainedSelfQuadrupleAddition node data j hj a hquad hstage

/-- The quadruple-depth formula domain in the original arithmetic relative self-product. -/
def arithmeticSelfQuadrupleOpen : (pullback fa fa).Opens := P ⁻¹ᵁ V

local notation "D" => arithmeticSelfQuadrupleOpen node data m j hj a hquad

/-- Construct the quadruple-depth output in the original final smooth model. -/
def arithmeticSelfQuadrupleAddition : (D).toScheme ⟶ (U).toScheme := (P ∣_ V) ≫ add

/-- The quadruple-depth output preserves the first original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticSelfQuadrupleAddition_structure :
    arithmeticSelfQuadrupleAddition node data m j hj a hquad hstage ≫ t =
      (D).ι ≫ pullback.fst fa fa ≫ fa ≫ q := by
  rw [arithmeticSelfQuadrupleAddition, Category.assoc,
    retainedSelfQuadrupleAddition_structure, morphismRestrict_ι_assoc,
    finiteResolvedAtlasPairInput_fst_assoc, arithmeticAtlasPairPresentation_structure]
  simp only [Category.assoc, arithmeticSelfQuadrupleOpen]

/-- The same output preserves the second original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticSelfQuadrupleAddition_structure_snd :
    arithmeticSelfQuadrupleAddition node data m j hj a hquad hstage ≫ t =
      (D).ι ≫ pullback.snd fa fa ≫ fa ≫ q := by
  rw [arithmeticSelfQuadrupleAddition_structure, pullback.condition_assoc]

/-- The quadruple and reciprocal outputs cover punctured inputs without denominator premises. -/
theorem arithmeticSelfQuadruple_or_reciprocal_mem
    (hk : 0 < depth) (p : (pullback fa fa : Scheme))
    (hx : al (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6) ∉ (input p).asIdeal)
    (hu : ar (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6) ∉ (input p).asIdeal) :
    p ∈ D ∨ p ∈ E :=
  retainedSelfQuadruple_or_reciprocal_mem node data j hj a
    hk hquad (P p)
    (arithmeticSelfFormulaInput_parameter_mem node data m j hj a p) hx hu

/-- The quadruple and reciprocal domains cover the whole punctured arithmetic open. -/
theorem arithmeticSelfQuadruplePuncturedOpen_le
    (hk : 0 < depth) :
    arithmeticSelfPuncturedOpen node data m j hj a ≤ D ⊔ E := by
  intro p hp
  exact arithmeticSelfQuadruple_or_reciprocal_mem node data m j hj a hquad
    hk p hp.1 hp.2

end Quadruple

end FLT.Mazur.WeierstrassDividedDepth
