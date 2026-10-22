/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedZeroSelfLocalCover

/-!
# Full smooth coverage of the creation-zero self-pair at depth two

Restrict the five actual source images to the original smooth pair scheme.
Every chart retains its complete quotient output and unchanged input maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m : ℕ) (hi : 1 ≤ n)
  (hm : 2 = depth)
local notation "j" => 0
local notation "hj" => hi
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "a" => retainedOlderFormulaIndex (j + 1) j (Nat.lt_succ_self j)
local notation "chart" => arithmeticTensorAtlasMap hπ data m (j + 1) hj
local notation "s" => finiteGlobalArithmeticStructure hπ data (j + 1) hj m
local notation "old" => finiteArithmeticNewestTensorChart hπ data m j hj
local notation "next" => finiteArithmeticDividedTensorChart hπ data m (j + 1) hj
local notation "E" => finiteDividedTensorAtlasIso hπ data Q (j + 1) hj
local notation "f" => chart a ≫ s
local notation "f₀" => old ≫ s
local notation "f'" => next ≫ s
local notation "g'" => chart 1 ≫ s
local notation "coords" => arithmeticLastRetainedIndexedCoordinates node data m j hj

local instance arithmeticLastRetainedZeroSelfSmoothCover_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data (j + 1) hj m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

local notation "base" => finiteGlobalStructure hπ data (j + 1) hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "X" => arithmeticLastRetainedZeroSelfLocalSource node data m hi
local notation "inc" => arithmeticLastRetainedZeroSelfLocalInclusion node data m hi

/-- The open where the original inputs are smooth at the original arithmetic order. -/
def arithmeticLastRetainedZeroSelfPairSmoothOpen : (pullback f f).Opens :=
  (pullback.fst f f ≫ chart a) ⁻¹ᵁ (s).smoothLocus ⊓
    (pullback.snd f f ≫ chart a) ⁻¹ᵁ (s).smoothLocus

local notation "A" => arithmeticLastRetainedZeroSelfPairSmoothOpen node data m hi

/-- Restrict each genuine local image to the original smooth-pair scheme. -/
def arithmeticLastRetainedZeroSelfSmoothChart
    (b : LastRetainedZeroSelfLocalIndex) : (A).toScheme.Opens :=
  (A).ι ⁻¹ᵁ (inc b).opensRange

local notation "C" => arithmeticLastRetainedZeroSelfSmoothChart node data m hi

/-- Recover the complete original source from its open image. -/
def arithmeticLastRetainedZeroSelfSmoothLift
    (b : LastRetainedZeroSelfLocalIndex) : (C b).toScheme ⟶ X b :=
  ((A).ι ∣_ (inc b).opensRange) ≫ (inc b).isoOpensRange.inv

local notation "lift" => arithmeticLastRetainedZeroSelfSmoothLift node data m hi

/-- Both entire original inputs are preserved by the restricted source lift. -/
@[reassoc] theorem arithmeticLastRetainedZeroSelfSmoothLift_inclusion
    (b : LastRetainedZeroSelfLocalIndex) :
    lift b ≫ inc b = (C b).ι ≫ (A).ι := by
  rw [arithmeticLastRetainedZeroSelfSmoothLift, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
  rfl

/-- Every smooth-pair chart carries its full constructed arithmetic quotient output. -/
def arithmeticLastRetainedZeroSelfSmoothOutput
    (b : LastRetainedZeroSelfLocalIndex) :
    (C b).toScheme ⟶ pullback q t :=
  lift b ≫ arithmeticLastRetainedZeroSelfLocalOutput node data m hi hm b

/-- Restriction preserves the whole original coefficient morphism, including nilpotents. -/
@[reassoc] theorem arithmeticLastRetainedZeroSelfSmoothOutput_base
    (b : LastRetainedZeroSelfLocalIndex) :
    arithmeticLastRetainedZeroSelfSmoothOutput node data m hi hm b ≫ pullback.fst q t =
      (C b).ι ≫ (A).ι ≫ pullback.fst f f ≫ f := by
  rw [arithmeticLastRetainedZeroSelfSmoothOutput, Category.assoc,
    arithmeticLastRetainedZeroSelfLocalOutput_base,
    arithmeticLastRetainedZeroSelfSmoothLift_inclusion_assoc]

include hm in
/-- These actual five output charts cover every smooth equal last-retained middle pair. -/
theorem arithmeticLastRetainedZeroSelfSmoothChart_covers
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (⨆ b, C b) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨b, z, hz⟩ := arithmeticLastRetainedZeroSelfLocal_exists
    node data m hi hm hgen p.val p.property.1 p.property.2
  exact (le_iSup (fun b => C b) b) (show p ∈ C b from ⟨z, hz⟩)

/-- A genuine open cover of the whole smooth pair, with the five outputs constructed above. -/
def arithmeticLastRetainedZeroSelfSmoothCover
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (A).toScheme.OpenCover :=
  (A).toScheme.openCoverOfIsOpenCover C
    (arithmeticLastRetainedZeroSelfSmoothChart_covers node data m hi hm hgen)

end FLT.Mazur.WeierstrassDividedDepth
