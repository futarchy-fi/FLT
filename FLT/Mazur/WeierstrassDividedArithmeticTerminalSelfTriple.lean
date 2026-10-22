/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalSelfReciprocal
public import FLT.Mazur.WeierstrassDividedTerminalSelfTripleAddition
public import FLT.Mazur.WeierstrassDividedArithmeticAtlasRelativeSmooth

/-!
# Complete arithmetic terminal self-pair coverage at triple depth

The intermediate formula at offset zero and the reciprocal formula exhaust
all relatively smooth terminal pairs at positive stage and triple node depth.
The constructed output retains the original arithmetic quotient coefficients.
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
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n nodeDepth : ℕ}
  (node : SplitNodeDepth W π nodeDepth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n)
local notation "hπ" => node.uniformizer_ne_zero
local notation "idx" => (1 : Fin (j + 3))
local notation "depth" => j
local notation "d" => data ⟨depth, Nat.lt_succ_of_le hj⟩
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

local notation "input" => arithmeticTerminalSelfReciprocalFormulaInput hπ data m j hj
local notation "al" => dividedPairLeft W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6
local notation "ar" => dividedPairRight W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6

local notation "E" => arithmeticTerminalSelfReciprocalOpen hπ data m j hj

variable (hj0 : 0 < j) (hdepth : nodeDepth = 3 * j)
local notation "V" => terminalSelfTripleOpen node data j hj hdepth
local notation "add" => terminalSelfTripleAddition node data j hj hdepth

/-- The triple-depth formula domain in the original arithmetic relative self-product. -/
def arithmeticTerminalSelfTripleOpen : (pullback fa fa).Opens := P ⁻¹ᵁ V

local notation "D" => arithmeticTerminalSelfTripleOpen node data m j hj hdepth

/-- Construct the triple-depth output in the original final smooth model. -/
def arithmeticTerminalSelfTripleAddition : (D).toScheme ⟶ (U).toScheme := (P ∣_ V) ≫ add

/-- The triple-depth output preserves the first original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticTerminalSelfTripleAddition_structure :
    arithmeticTerminalSelfTripleAddition node data m j hj hdepth ≫ t =
      (D).ι ≫ pullback.fst fa fa ≫ fa ≫ q := by
  rw [arithmeticTerminalSelfTripleAddition, Category.assoc,
    terminalSelfTripleAddition_structure, morphismRestrict_ι_assoc,
    finiteResolvedAtlasPairInput_fst_assoc, arithmeticAtlasPairPresentation_structure]
  simp only [Category.assoc, arithmeticTerminalSelfTripleOpen]

/-- The same output preserves the second original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticTerminalSelfTripleAddition_structure_snd :
    arithmeticTerminalSelfTripleAddition node data m j hj hdepth ≫ t =
      (D).ι ≫ pullback.snd fa fa ≫ fa ≫ q := by
  rw [arithmeticTerminalSelfTripleAddition_structure, pullback.condition_assoc]

include hj0 in
/-- Every smooth terminal pair reaches a triple-depth or reciprocal output at the original order. -/
theorem arithmeticTerminalSelfTriple_or_reciprocal_mem
    (p : (pullback fa fa : Scheme)) : p ∈ D ∨ p ∈ E := by
  have hp := arithmeticTerminalSelfFormulaInput_punctured hπ data m j hj node
    hj0 (by omega) p
  exact terminalSelfTriple_or_reciprocal_mem node data j hj hj0 hdepth (P p)
    (arithmeticTerminalSelfFormulaInput_parameter_mem hπ data m j hj p) hp.1 hp.2

include hj0 in
/-- The two constructed domains exhaust the entire smooth terminal relative self-product. -/
theorem arithmeticTerminalSelfTriple_cover_top : D ⊔ E = ⊤ := by
  apply top_unique
  intro p _
  exact arithmeticTerminalSelfTriple_or_reciprocal_mem node data m j hj hj0 hdepth p

/-- The output lives over the original arithmetic quotient, retaining nilpotents. -/
def arithmeticTerminalSelfTripleQuotientOutput : (D).toScheme ⟶ pullback q t :=
  pullback.lift ((D).ι ≫ pullback.fst fa fa ≫ fa)
    (arithmeticTerminalSelfTripleAddition node data m j hj hdepth)
    (by simpa only [Category.assoc] using
      (arithmeticTerminalSelfTripleAddition_structure node data m j hj hdepth).symm)

/-- The quotient output preserves the whole original coefficient morphism. -/
@[reassoc] theorem arithmeticTerminalSelfTripleQuotientOutput_base :
    arithmeticTerminalSelfTripleQuotientOutput node data m j hj hdepth ≫ pullback.fst q t =
      (D).ι ≫ pullback.fst fa fa ≫ fa := by
  simp only [arithmeticTerminalSelfTripleQuotientOutput, pullback.lift_fst]

/-- Integral projection recovers the entire triple-depth output. -/
@[reassoc] theorem arithmeticTerminalSelfTripleQuotientOutput_integral :
    arithmeticTerminalSelfTripleQuotientOutput node data m j hj hdepth ≫ pullback.snd q t =
      arithmeticTerminalSelfTripleAddition node data m j hj hdepth := by
  simp only [arithmeticTerminalSelfTripleQuotientOutput, pullback.lift_snd]

local notation "f" => chart idx ≫ s
local instance arithmeticTerminalSelfTriple_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data j hj m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

include hj0 in
/-- Full relatively smooth terminal inputs reach actual domains with both coordinates intact. -/
theorem arithmeticTerminalSelfTriple_target (p : (pullback f f : Scheme))
    (hs : chart idx (pullback.fst f f p) ∈ (s).smoothLocus)
    (ht : chart idx (pullback.snd f f p) ∈ (s).smoothLocus) :
    ∃ z : (pullback fa fa : Scheme),
      (O).ι (pullback.fst fa fa z) = pullback.fst f f p ∧
      (O).ι (pullback.snd fa fa z) = pullback.snd f f p ∧ (z ∈ D ∨ z ∈ E) := by
  obtain ⟨z, hz, he⟩ := arithmeticAtlasRelativePair_exists hπ data m j hj idx idx p hs ht
  exact ⟨z, hz, he,
    arithmeticTerminalSelfTriple_or_reciprocal_mem node data m j hj hj0 hdepth z⟩

end FLT.Mazur.WeierstrassDividedDepth
