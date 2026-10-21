/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticSelfIntermediateAddition
public import FLT.Mazur.WeierstrassDividedRetainedSelfShallowAddition
public import FLT.Mazur.WeierstrassDividedRetainedSelfDeepAddition

/-!
# Shallow and deep arithmetic self-pair coverage

At every arithmetic order, the shallow or deep constructed output and the
reciprocal output cover the full punctured input open in the stated range.
The deep output retains its necessary doubled-stage bound.
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

section Shallow
variable (hlo : 2 * (retainedSelfFormulaDepth j a) < nodeDepth)
  (hhi : nodeDepth < 3 * (retainedSelfFormulaDepth j a))
local notation "V" => retainedSelfShallowOpen node data j hj a hlo hhi
local notation "add" => retainedSelfShallowAddition node data j hj a hlo hhi

/-- The shallow formula domain in the original arithmetic relative self-product. -/
def arithmeticSelfShallowOpen : (pullback fa fa).Opens := P ⁻¹ᵁ V

local notation "D" => arithmeticSelfShallowOpen node data m j hj a hlo hhi

/-- Construct the shallow output in the original final smooth model. -/
def arithmeticSelfShallowAddition : (D).toScheme ⟶ (U).toScheme := (P ∣_ V) ≫ add

/-- The shallow output preserves the first original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticSelfShallowAddition_structure :
    arithmeticSelfShallowAddition node data m j hj a hlo hhi ≫ t =
      (D).ι ≫ pullback.fst fa fa ≫ fa ≫ q := by
  rw [arithmeticSelfShallowAddition, Category.assoc,
    retainedSelfShallowAddition_structure, morphismRestrict_ι_assoc,
    finiteResolvedAtlasPairInput_fst_assoc, arithmeticAtlasPairPresentation_structure]
  simp only [Category.assoc, arithmeticSelfShallowOpen]

/-- The same output preserves the second original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticSelfShallowAddition_structure_snd :
    arithmeticSelfShallowAddition node data m j hj a hlo hhi ≫ t =
      (D).ι ≫ pullback.snd fa fa ≫ fa ≫ q := by
  rw [arithmeticSelfShallowAddition_structure, pullback.condition_assoc]

/-- The shallow and reciprocal outputs cover punctured inputs without denominator premises. -/
theorem arithmeticSelfShallow_or_reciprocal_mem
    (p : (pullback fa fa : Scheme))
    (hx : al (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6) ∉ (input p).asIdeal)
    (hu : ar (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6) ∉ (input p).asIdeal) :
    p ∈ D ∨ p ∈ E :=
  retainedSelfShallow_or_reciprocal_mem node data j hj a
    hlo hhi (P p)
    (arithmeticSelfFormulaInput_parameter_mem node data m j hj a p) hx hu

/-- The shallow and reciprocal domains cover the whole original punctured arithmetic open. -/
theorem arithmeticSelfShallowPuncturedOpen_le :
    arithmeticSelfPuncturedOpen node data m j hj a ≤ D ⊔ E := by
  intro p hp
  exact arithmeticSelfShallow_or_reciprocal_mem node data m j hj a hlo hhi
    p hp.1 hp.2

end Shallow

section Deep
variable
  (hstage : (retainedSelfFormulaDepth j a) + (retainedSelfFormulaDepth j a) ≤ j)
local notation "V" => retainedSelfDeepOpen node data j hj a hstage
local notation "add" => retainedSelfDeepAddition node data j hj a hstage

/-- The deep formula domain in the original arithmetic relative self-product. -/
def arithmeticSelfDeepOpen : (pullback fa fa).Opens := P ⁻¹ᵁ V

local notation "D" => arithmeticSelfDeepOpen node data m j hj a hstage

/-- Construct the deep output in the original final smooth model. -/
def arithmeticSelfDeepAddition : (D).toScheme ⟶ (U).toScheme := (P ∣_ V) ≫ add

/-- The deep output preserves the first original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticSelfDeepAddition_structure :
    arithmeticSelfDeepAddition node data m j hj a hstage ≫ t =
      (D).ι ≫ pullback.fst fa fa ≫ fa ≫ q := by
  rw [arithmeticSelfDeepAddition, Category.assoc,
    retainedSelfDeepAddition_structure, morphismRestrict_ι_assoc,
    finiteResolvedAtlasPairInput_fst_assoc, arithmeticAtlasPairPresentation_structure]
  simp only [Category.assoc, arithmeticSelfDeepOpen]

/-- The same output preserves the second original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticSelfDeepAddition_structure_snd :
    arithmeticSelfDeepAddition node data m j hj a hstage ≫ t =
      (D).ι ≫ pullback.snd fa fa ≫ fa ≫ q := by
  rw [arithmeticSelfDeepAddition_structure, pullback.condition_assoc]

/-- The deep and reciprocal outputs cover punctured inputs without denominator premises. -/
theorem arithmeticSelfDeep_or_reciprocal_mem
    (hk : 0 < depth) (hdeep : 4 * depth < nodeDepth) (p : (pullback fa fa : Scheme))
    (hx : al (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6) ∉ (input p).asIdeal)
    (hu : ar (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6) ∉ (input p).asIdeal) :
    p ∈ D ∨ p ∈ E :=
  retainedSelfDeep_or_reciprocal_mem node data j hj a
    hk hdeep hstage (P p)
    (arithmeticSelfFormulaInput_parameter_mem node data m j hj a p) hx hu

/-- The deep and reciprocal domains cover the whole original punctured arithmetic open. -/
theorem arithmeticSelfDeepPuncturedOpen_le
    (hk : 0 < depth) (hdeep : 4 * depth < nodeDepth) :
    arithmeticSelfPuncturedOpen node data m j hj a ≤ D ⊔ E := by
  intro p hp
  exact arithmeticSelfDeep_or_reciprocal_mem node data m j hj a hstage
    hk hdeep p hp.1 hp.2

end Deep

end FLT.Mazur.WeierstrassDividedDepth
