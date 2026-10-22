/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedZeroSelfOddLocalCover

/-!
# Full smooth coverage of the creation-zero self-pair at depth three

Restrict the seven actual source images to the original smooth pair scheme.
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
  (hodd : depth = 3)
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

local instance arithmeticLastRetainedZeroSelfOddSmoothCover_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data (j + 1) hj m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

local notation "base" => finiteGlobalStructure hπ data (j + 1) hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "X" => arithmeticLastRetainedZeroSelfOddLocalSource node data m hi hodd
local notation "inc" => arithmeticLastRetainedZeroSelfOddLocalInclusion node data m hi hodd

/-- The open where the original inputs are smooth at the original arithmetic order. -/
def arithmeticLastRetainedZeroSelfOddPairSmoothOpen : (pullback f f).Opens :=
  (pullback.fst f f ≫ chart a) ⁻¹ᵁ (s).smoothLocus ⊓
    (pullback.snd f f ≫ chart a) ⁻¹ᵁ (s).smoothLocus

local notation "A" => arithmeticLastRetainedZeroSelfOddPairSmoothOpen node data m hi

/-- Restrict each genuine local image to the original smooth-pair scheme. -/
def arithmeticLastRetainedZeroSelfOddSmoothChart
    (b : LastRetainedZeroSelfOddLocalIndex) : (A).toScheme.Opens :=
  (A).ι ⁻¹ᵁ (inc b).opensRange

local notation "C" => arithmeticLastRetainedZeroSelfOddSmoothChart node data m hi hodd

/-- Recover the complete original source from its open image. -/
def arithmeticLastRetainedZeroSelfOddSmoothLift
    (b : LastRetainedZeroSelfOddLocalIndex) : (C b).toScheme ⟶ X b :=
  ((A).ι ∣_ (inc b).opensRange) ≫ (inc b).isoOpensRange.inv

local notation "lift" => arithmeticLastRetainedZeroSelfOddSmoothLift node data m hi hodd

/-- Both entire original inputs are preserved by the restricted source lift. -/
@[reassoc] theorem arithmeticLastRetainedZeroSelfOddSmoothLift_inclusion
    (b : LastRetainedZeroSelfOddLocalIndex) :
    lift b ≫ inc b = (C b).ι ≫ (A).ι := by
  rw [arithmeticLastRetainedZeroSelfOddSmoothLift, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
  rfl

/-- Every smooth-pair chart carries its full constructed arithmetic quotient output. -/
def arithmeticLastRetainedZeroSelfOddSmoothOutput
    (b : LastRetainedZeroSelfOddLocalIndex) :
    (C b).toScheme ⟶ pullback q t :=
  lift b ≫ arithmeticLastRetainedZeroSelfOddLocalOutput node data m hi hodd b

/-- Restriction preserves the whole original coefficient morphism, including nilpotents. -/
@[reassoc] theorem arithmeticLastRetainedZeroSelfOddSmoothOutput_base
    (b : LastRetainedZeroSelfOddLocalIndex) :
    arithmeticLastRetainedZeroSelfOddSmoothOutput node data m hi hodd b ≫ pullback.fst q t =
      (C b).ι ≫ (A).ι ≫ pullback.fst f f ≫ f := by
  rw [arithmeticLastRetainedZeroSelfOddSmoothOutput, Category.assoc,
    arithmeticLastRetainedZeroSelfOddLocalOutput_base,
    arithmeticLastRetainedZeroSelfOddSmoothLift_inclusion_assoc]

include hodd in
/-- These actual seven output charts cover every smooth equal last-retained odd pair. -/
theorem arithmeticLastRetainedZeroSelfOddSmoothChart_covers
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (⨆ b, C b) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨b, z, hz⟩ := arithmeticLastRetainedZeroSelfOddLocal_exists
    node data m hi hodd hgen p.val p.property.1 p.property.2
  exact (le_iSup (fun b => C b) b) (show p ∈ C b from ⟨z, hz⟩)

/-- A genuine open cover of the whole smooth pair, with the seven outputs constructed above. -/
def arithmeticLastRetainedZeroSelfOddSmoothCover
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (A).toScheme.OpenCover :=
  (A).toScheme.openCoverOfIsOpenCover C
    (arithmeticLastRetainedZeroSelfOddSmoothChart_covers node data m hi hodd hgen)

end FLT.Mazur.WeierstrassDividedDepth
