/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalSelfReciprocal
public import FLT.Mazur.WeierstrassDividedTerminalSelfShallowAddition
public import FLT.Mazur.WeierstrassDividedArithmeticAtlasRelativeSmooth

/-!
# Complete arithmetic terminal self-pair coverage in the shallow range

Relative smoothness supplies both punctures. The shallow and reciprocal
output domains therefore cover the entire terminal pair, including its
diagonal, without any coordinate or branch hypothesis.
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

variable (hlo : 2 * (j) < nodeDepth)
  (hhi : nodeDepth < 3 * (j))
local notation "V" => terminalSelfShallowOpen node data j hj hlo hhi
local notation "add" => terminalSelfShallowAddition node data j hj hlo hhi

/-- The shallow formula domain in the original arithmetic relative self-product. -/
def arithmeticTerminalSelfShallowOpen : (pullback fa fa).Opens := P ⁻¹ᵁ V

local notation "D" => arithmeticTerminalSelfShallowOpen node data m j hj hlo hhi

/-- Construct the shallow output in the original final smooth model. -/
def arithmeticTerminalSelfShallowAddition : (D).toScheme ⟶ (U).toScheme := (P ∣_ V) ≫ add

/-- The shallow output preserves the first original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticTerminalSelfShallowAddition_structure :
    arithmeticTerminalSelfShallowAddition node data m j hj hlo hhi ≫ t =
      (D).ι ≫ pullback.fst fa fa ≫ fa ≫ q := by
  rw [arithmeticTerminalSelfShallowAddition, Category.assoc,
    terminalSelfShallowAddition_structure, morphismRestrict_ι_assoc,
    finiteResolvedAtlasPairInput_fst_assoc, arithmeticAtlasPairPresentation_structure]
  simp only [Category.assoc, arithmeticTerminalSelfShallowOpen]

/-- The same output preserves the second original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticTerminalSelfShallowAddition_structure_snd :
    arithmeticTerminalSelfShallowAddition node data m j hj hlo hhi ≫ t =
      (D).ι ≫ pullback.snd fa fa ≫ fa ≫ q := by
  rw [arithmeticTerminalSelfShallowAddition_structure, pullback.condition_assoc]

/-- Every smooth terminal pair reaches a shallow or reciprocal output at the original order. -/
theorem arithmeticTerminalSelfShallow_or_reciprocal_mem
    (p : (pullback fa fa : Scheme)) : p ∈ D ∨ p ∈ E := by
  have hp := arithmeticTerminalSelfFormulaInput_punctured hπ data m j hj node
    (by omega) hlo p
  exact terminalSelfShallow_or_reciprocal_mem node data j hj hlo hhi (P p)
    (arithmeticTerminalSelfFormulaInput_parameter_mem hπ data m j hj p) hp.1 hp.2

/-- The two constructed domains exhaust the entire smooth terminal relative self-product. -/
theorem arithmeticTerminalSelfShallow_cover_top : D ⊔ E = ⊤ := by
  apply top_unique
  intro p _
  exact arithmeticTerminalSelfShallow_or_reciprocal_mem node data m j hj hlo hhi p

/-- The shallow output lives over the original arithmetic quotient, with nilpotents retained. -/
def arithmeticTerminalSelfShallowQuotientOutput : (D).toScheme ⟶ pullback q t :=
  pullback.lift ((D).ι ≫ pullback.fst fa fa ≫ fa)
    (arithmeticTerminalSelfShallowAddition node data m j hj hlo hhi)
    (by simpa only [Category.assoc] using
      (arithmeticTerminalSelfShallowAddition_structure node data m j hj hlo hhi).symm)

/-- The quotient output preserves the whole original coefficient morphism. -/
@[reassoc] theorem arithmeticTerminalSelfShallowQuotientOutput_base :
    arithmeticTerminalSelfShallowQuotientOutput node data m j hj hlo hhi ≫ pullback.fst q t =
      (D).ι ≫ pullback.fst fa fa ≫ fa := by
  simp only [arithmeticTerminalSelfShallowQuotientOutput, pullback.lift_fst]

/-- Integral projection recovers the entire shallow output. -/
@[reassoc] theorem arithmeticTerminalSelfShallowQuotientOutput_integral :
    arithmeticTerminalSelfShallowQuotientOutput node data m j hj hlo hhi ≫ pullback.snd q t =
      arithmeticTerminalSelfShallowAddition node data m j hj hlo hhi := by
  simp only [arithmeticTerminalSelfShallowQuotientOutput, pullback.lift_snd]

/-- The reciprocal alternative likewise lifts to the original arithmetic quotient. -/
def arithmeticTerminalSelfReciprocalQuotientOutput : (E).toScheme ⟶ pullback q t :=
  pullback.lift ((E).ι ≫ pullback.fst fa fa ≫ fa)
    (arithmeticTerminalSelfReciprocalAddition hπ data m j hj)
    (by simpa only [Category.assoc] using
      (arithmeticTerminalSelfReciprocalAddition_structure hπ data m j hj).symm)

/-- The reciprocal quotient output keeps the same complete coefficient morphism. -/
@[reassoc] theorem arithmeticTerminalSelfReciprocalQuotientOutput_base :
    arithmeticTerminalSelfReciprocalQuotientOutput node data m j hj ≫ pullback.fst q t =
      (E).ι ≫ pullback.fst fa fa ≫ fa := by
  simp only [arithmeticTerminalSelfReciprocalQuotientOutput, pullback.lift_fst]

/-- Integral projection recovers the entire reciprocal output. -/
@[reassoc] theorem arithmeticTerminalSelfReciprocalQuotientOutput_integral :
    arithmeticTerminalSelfReciprocalQuotientOutput node data m j hj ≫ pullback.snd q t =
      arithmeticTerminalSelfReciprocalAddition hπ data m j hj := by
  simp only [arithmeticTerminalSelfReciprocalQuotientOutput, pullback.lift_snd]

local notation "f" => chart idx ≫ s
local instance arithmeticTerminalSelfShallow_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data j hj m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- Full relatively smooth terminal inputs reach actual domains with both coordinates intact. -/
theorem arithmeticTerminalSelfShallow_target (p : (pullback f f : Scheme))
    (hs : chart idx (pullback.fst f f p) ∈ (s).smoothLocus)
    (ht : chart idx (pullback.snd f f p) ∈ (s).smoothLocus) :
    ∃ z : (pullback fa fa : Scheme),
      (O).ι (pullback.fst fa fa z) = pullback.fst f f p ∧
      (O).ι (pullback.snd fa fa z) = pullback.snd f f p ∧ (z ∈ D ∨ z ∈ E) := by
  obtain ⟨z, hz, he⟩ := arithmeticAtlasRelativePair_exists hπ data m j hj idx idx p hs ht
  exact ⟨z, hz, he,
    arithmeticTerminalSelfShallow_or_reciprocal_mem node data m j hj hlo hhi z⟩

end FLT.Mazur.WeierstrassDividedDepth
