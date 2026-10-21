/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticSelfReciprocalAddition
public import FLT.Mazur.WeierstrassDividedRetainedSelfIntermediateAddition
public import FLT.Mazur.SchemeArithmeticCoefficientSupport

/-!
# Intermediate coverage for original arithmetic self-pairs

The intermediate and reciprocal outputs cover punctured retained self-pairs
in the intermediate range at every arithmetic order. Closed-fiber support
comes from the original quotient map, including nonreduced quotients.
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

/-- The full arithmetic self-pair coordinates keep the original coefficient morphism. -/
@[reassoc] theorem arithmeticSelfFormulaInput_structure :
    input ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      pullback.fst fa fa ≫ fa ≫ q := by
  rw [arithmeticSelfReciprocalFormulaInput, Category.assoc, retainedSelfFormulaInput,
    atlasPairFormulaInput_structure, finiteResolvedAtlasPairInput_fst_assoc,
    arithmeticAtlasPairPresentation_structure]

/-- Every original arithmetic self-pair prime contains the uniformizer. -/
theorem arithmeticSelfFormulaInput_parameter_mem (p : (pullback fa fa : Scheme)) :
    algebraMap R A π ∈ (input p).asIdeal :=
  spectrumInput_parameter_mem π m input (pullback.fst fa fa ≫ fa)
    (by simpa only [Category.assoc] using
      arithmeticSelfFormulaInput_structure node data m j hj a) p

variable (hdepth : 3 * (retainedSelfFormulaDepth j a) ≤ nodeDepth)
  (hm : nodeDepth < 4 * (retainedSelfFormulaDepth j a))
 
  (hstage : (retainedSelfFormulaDepth j a) + (nodeDepth - 3 * (retainedSelfFormulaDepth j a)) ≤ j)
local notation "V" => retainedSelfIntermediateOpen node data j hj a hdepth hm hstage
local notation "add" => retainedSelfIntermediateAddition node data j hj a hdepth hm hstage

/-- The intermediate domain in the actual full arithmetic self-pair. -/
def arithmeticSelfIntermediateOpen : (pullback fa fa).Opens := P ⁻¹ᵁ V

local notation "D" => arithmeticSelfIntermediateOpen node data m j hj a hdepth hm hstage

/-- The constructed output lies in the original final resolved smooth model. -/
def arithmeticSelfIntermediateAddition : (D).toScheme ⟶ (U).toScheme := (P ∣_ V) ≫ add

/-- The output retains exactly the first input's actual arithmetic coefficient point. -/
@[reassoc] theorem arithmeticSelfIntermediateAddition_structure :
    arithmeticSelfIntermediateAddition node data m j hj a hdepth hm hstage ≫ t =
      (D).ι ≫ pullback.fst fa fa ≫ fa ≫ q := by
  rw [arithmeticSelfIntermediateAddition, Category.assoc,
    retainedSelfIntermediateAddition_structure, morphismRestrict_ι_assoc,
    finiteResolvedAtlasPairInput_fst_assoc, arithmeticAtlasPairPresentation_structure]
  simp only [Category.assoc, arithmeticSelfIntermediateOpen]

/-- The same output retains the second original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticSelfIntermediateAddition_structure_snd :
    arithmeticSelfIntermediateAddition node data m j hj a hdepth hm hstage ≫ t =
      (D).ι ≫ pullback.snd fa fa ≫ fa ≫ q := by
  rw [arithmeticSelfIntermediateAddition_structure, pullback.condition_assoc]

local notation "E" => arithmeticSelfReciprocalOpen hπ data m j hj a

/-- Both actual formula domains cover every punctured arithmetic self-pair in this range. -/
theorem arithmeticSelfIntermediate_or_reciprocal_mem (p : (pullback fa fa : Scheme))
    (hx : al (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6) ∉ (input p).asIdeal)
    (hu : ar (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6) ∉ (input p).asIdeal) :
    p ∈ D ∨ p ∈ E :=
  retainedSelfIntermediate_or_reciprocal_mem node data j hj a hdepth hm hstage (P p)
    (arithmeticSelfFormulaInput_parameter_mem node data m j hj a p) hx hu

local notation "x₁" => al (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "x₂" => ar (x W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "y₁" => al (y W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)
local notation "y₂" => ar (y W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6)

/-- Coincident residue coordinates use the actual arithmetic tangent domain. -/
theorem arithmeticSelfIntermediateOpen_equal_mem (p : (pullback fa fa : Scheme))
    (hx : x₁ - x₂ ∈ (input p).asIdeal) (hy : y₁ - y₂ ∈ (input p).asIdeal)
    (hu : x₁ ∉ (input p).asIdeal) : p ∈ D :=
  retainedSelfIntermediateOpen_equal_mem node data j hj a hdepth hm hstage (P p)
    (arithmeticSelfFormulaInput_parameter_mem node data m j hj a p) hx hy hu

/-- Distinct punctured residue abscissae use the actual arithmetic secant domain. -/
theorem arithmeticSelfIntermediateOpen_distinct_mem (p : (pullback fa fa : Scheme))
    (hx : x₁ - x₂ ∉ (input p).asIdeal)
    (hu : x₁ ∉ (input p).asIdeal) (hv : x₂ ∉ (input p).asIdeal) : p ∈ D :=
  retainedSelfIntermediateOpen_distinct_mem node data j hj a hdepth hm hstage (P p)
    (arithmeticSelfFormulaInput_parameter_mem node data m j hj a p) hx hu hv

/-- The actual open subset on which both arithmetic input abscissae are punctured. -/
def arithmeticSelfPuncturedOpen : (pullback fa fa).Opens :=
  input ⁻¹ᵁ (PrimeSpectrum.basicOpen x₁ ⊓ PrimeSpectrum.basicOpen x₂)

/-- The two constructed output domains cover the entire arithmetic punctured open. -/
theorem arithmeticSelfPuncturedOpen_le :
    arithmeticSelfPuncturedOpen node data m j hj a ≤ D ⊔ E := by
  intro p hp
  exact arithmeticSelfIntermediate_or_reciprocal_mem node data m j hj a hdepth hm hstage
    p hp.1 hp.2

end FLT.Mazur.WeierstrassDividedDepth
