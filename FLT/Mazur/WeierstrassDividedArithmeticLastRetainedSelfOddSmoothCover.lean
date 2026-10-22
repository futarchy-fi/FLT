/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedSelfOddLocalCover

/-!
# A full smooth equal last-retained middle open cover

Restrict the twelve actual source images to the original smooth pair scheme.
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
  (m i : ℕ) (hi : i + 2 ≤ n)
  (hodd : depth = 2 * (i + 2) + 1)
local notation "j" => i + 1
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




local instance arithmeticLastRetainedSelfOddSmoothCover_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data (j + 1) hj m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

local notation "base" => finiteGlobalStructure hπ data (j + 1) hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "X" => arithmeticLastRetainedSelfOddLocalSource node data m i hi hodd
local notation "inc" => arithmeticLastRetainedSelfOddLocalInclusion node data m i hi hodd

/-- The open where the original inputs are smooth at the original arithmetic order. -/
def arithmeticLastRetainedSelfOddPairSmoothOpen : (pullback f f).Opens :=
  (pullback.fst f f ≫ chart a) ⁻¹ᵁ (s).smoothLocus ⊓
    (pullback.snd f f ≫ chart a) ⁻¹ᵁ (s).smoothLocus

local notation "A" => arithmeticLastRetainedSelfOddPairSmoothOpen node data m i hi

/-- Restrict each genuine local image to the original smooth-pair scheme. -/
def arithmeticLastRetainedSelfOddSmoothChart
    (b : LastRetainedSelfOddLocalIndex) : (A).toScheme.Opens :=
  (A).ι ⁻¹ᵁ (inc b).opensRange

local notation "C" => arithmeticLastRetainedSelfOddSmoothChart node data m i hi hodd

/-- Recover the complete original source from its open image. -/
def arithmeticLastRetainedSelfOddSmoothLift
    (b : LastRetainedSelfOddLocalIndex) : (C b).toScheme ⟶ X b :=
  ((A).ι ∣_ (inc b).opensRange) ≫ (inc b).isoOpensRange.inv

local notation "lift" => arithmeticLastRetainedSelfOddSmoothLift node data m i hi hodd

/-- Both entire original inputs are preserved by the restricted source lift. -/
@[reassoc] theorem arithmeticLastRetainedSelfOddSmoothLift_inclusion
    (b : LastRetainedSelfOddLocalIndex) :
    lift b ≫ inc b = (C b).ι ≫ (A).ι := by
  rw [arithmeticLastRetainedSelfOddSmoothLift, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
  rfl


/-- Every smooth-pair chart carries its full constructed arithmetic quotient output. -/
def arithmeticLastRetainedSelfOddSmoothOutput
    (b : LastRetainedSelfOddLocalIndex) :
    (C b).toScheme ⟶ pullback q t :=
  lift b ≫ arithmeticLastRetainedSelfOddLocalOutput node data m i hi hodd b

/-- Restriction preserves the whole original coefficient morphism, including nilpotents. -/
@[reassoc] theorem arithmeticLastRetainedSelfOddSmoothOutput_base
    (b : LastRetainedSelfOddLocalIndex) :
    arithmeticLastRetainedSelfOddSmoothOutput node data m i hi hodd b ≫ pullback.fst q t =
      (C b).ι ≫ (A).ι ≫ pullback.fst f f ≫ f := by
  rw [arithmeticLastRetainedSelfOddSmoothOutput, Category.assoc,
    arithmeticLastRetainedSelfOddLocalOutput_base,
    arithmeticLastRetainedSelfOddSmoothLift_inclusion_assoc]

/-- These actual twelve output charts cover every smooth equal last-retained odd pair. -/
theorem arithmeticLastRetainedSelfOddSmoothChart_covers
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (⨆ b, C b) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨b, z, hz⟩ := arithmeticLastRetainedSelfOddLocal_exists
    node data m i hi hodd hgen p.val p.property.1 p.property.2
  exact (le_iSup (fun b => C b) b) (show p ∈ C b from ⟨z, hz⟩)

/-- A genuine open cover of the whole smooth pair, with the twelve outputs constructed above. -/
def arithmeticLastRetainedSelfOddSmoothCover
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (A).toScheme.OpenCover :=
  (A).toScheme.openCoverOfIsOpenCover C
    (arithmeticLastRetainedSelfOddSmoothChart_covers node data m i hi hodd hgen)

end FLT.Mazur.WeierstrassDividedDepth
