/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedSelfLocalCover

/-!
# A full smooth equal last-retained middle open cover

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
  (m i : ℕ) (hi : i + 2 ≤ n)
  (hm : 2 * (i + 2) = depth)
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




local instance arithmeticLastRetainedSelfSmoothCover_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data (j + 1) hj m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

local notation "base" => finiteGlobalStructure hπ data (j + 1) hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "X" => arithmeticLastRetainedSelfLocalSource node data m i hi hm
local notation "inc" => arithmeticLastRetainedSelfLocalInclusion node data m i hi hm

/-- The open where the original inputs are smooth at the original arithmetic order. -/
def arithmeticLastRetainedSelfPairSmoothOpen : (pullback f f).Opens :=
  (pullback.fst f f ≫ chart a) ⁻¹ᵁ (s).smoothLocus ⊓
    (pullback.snd f f ≫ chart a) ⁻¹ᵁ (s).smoothLocus

local notation "A" => arithmeticLastRetainedSelfPairSmoothOpen node data m i hi

/-- Restrict each genuine local image to the original smooth-pair scheme. -/
def arithmeticLastRetainedSelfSmoothChart (b : LastRetainedSelfLocalIndex) : (A).toScheme.Opens :=
  (A).ι ⁻¹ᵁ (inc b).opensRange

local notation "C" => arithmeticLastRetainedSelfSmoothChart node data m i hi hm

/-- Recover the complete original source from its open image. -/
def arithmeticLastRetainedSelfSmoothLift (b : LastRetainedSelfLocalIndex) : (C b).toScheme ⟶ X b :=
  ((A).ι ∣_ (inc b).opensRange) ≫ (inc b).isoOpensRange.inv

local notation "lift" => arithmeticLastRetainedSelfSmoothLift node data m i hi hm

/-- Both entire original inputs are preserved by the restricted source lift. -/
@[reassoc] theorem arithmeticLastRetainedSelfSmoothLift_inclusion (b : LastRetainedSelfLocalIndex) :
    lift b ≫ inc b = (C b).ι ≫ (A).ι := by
  rw [arithmeticLastRetainedSelfSmoothLift, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
  rfl


/-- Every smooth-pair chart carries its full constructed arithmetic quotient output. -/
def arithmeticLastRetainedSelfSmoothOutput (b : LastRetainedSelfLocalIndex) :
    (C b).toScheme ⟶ pullback q t :=
  lift b ≫ arithmeticLastRetainedSelfLocalOutput node data m i hi hm b

/-- Restriction preserves the whole original coefficient morphism, including nilpotents. -/
@[reassoc] theorem arithmeticLastRetainedSelfSmoothOutput_base (b : LastRetainedSelfLocalIndex) :
    arithmeticLastRetainedSelfSmoothOutput node data m i hi hm b ≫ pullback.fst q t =
      (C b).ι ≫ (A).ι ≫ pullback.fst f f ≫ f := by
  rw [arithmeticLastRetainedSelfSmoothOutput, Category.assoc,
    arithmeticLastRetainedSelfLocalOutput_base,
    arithmeticLastRetainedSelfSmoothLift_inclusion_assoc]

include hm in
/-- These actual seven output charts cover every smooth equal last-retained middle pair. -/
theorem arithmeticLastRetainedSelfSmoothChart_covers
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (⨆ b, C b) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨b, z, hz⟩ := arithmeticLastRetainedSelfLocal_exists
    node data m i hi hm hgen p.val p.property.1 p.property.2
  exact (le_iSup (fun b => C b) b) (show p ∈ C b from ⟨z, hz⟩)

/-- A genuine open cover of the whole smooth pair, with the seven outputs constructed above. -/
def arithmeticLastRetainedSelfSmoothCover
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (A).toScheme.OpenCover :=
  (A).toScheme.openCoverOfIsOpenCover C
    (arithmeticLastRetainedSelfSmoothChart_covers node data m i hi hm hgen)

end FLT.Mazur.WeierstrassDividedDepth
