/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedMiddleLocal

/-!
# A full smooth last-retained/middle-terminal open cover

Restrict the two actual source images to the original smooth pair scheme.
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
  (m j : ℕ) (hj : j + 1 ≤ n)
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




local instance arithmeticLastRetainedMiddleSmoothCover_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data (j + 1) hj m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

local notation "base" => finiteGlobalStructure hπ data (j + 1) hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "X" => arithmeticLastRetainedMiddleLocalSource node data m j hj
local notation "inc" => arithmeticLastRetainedMiddleLocalInclusion node data m j hj

/-- The open where both original inputs are smooth at the original arithmetic order. -/
def arithmeticLastRetainedMiddlePairSmoothOpen : (pullback f g').Opens :=
  (pullback.fst f g' ≫ chart a) ⁻¹ᵁ (s).smoothLocus ⊓
    (pullback.snd f g' ≫ chart 1) ⁻¹ᵁ (s).smoothLocus

local notation "A" => arithmeticLastRetainedMiddlePairSmoothOpen node data m j hj

/-- Restrict each genuine local image to the original smooth-pair scheme. -/
def arithmeticLastRetainedMiddleSmoothChart (b : Bool) : (A).toScheme.Opens :=
  (A).ι ⁻¹ᵁ (inc b).opensRange

local notation "C" => arithmeticLastRetainedMiddleSmoothChart node data m j hj

/-- Recover the complete original source from its open image. -/
def arithmeticLastRetainedMiddleSmoothLift (b : Bool) : (C b).toScheme ⟶ X b :=
  ((A).ι ∣_ (inc b).opensRange) ≫ (inc b).isoOpensRange.inv

local notation "lift" => arithmeticLastRetainedMiddleSmoothLift node data m j hj

/-- Both entire original inputs are preserved by the restricted source lift. -/
@[reassoc] theorem arithmeticLastRetainedMiddleSmoothLift_inclusion (b : Bool) :
    lift b ≫ inc b = (C b).ι ≫ (A).ι := by
  rw [arithmeticLastRetainedMiddleSmoothLift, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
  rfl

variable (hm : 2 * (j + 1) = depth)

/-- Every smooth-pair chart carries its full constructed arithmetic quotient output. -/
def arithmeticLastRetainedMiddleSmoothOutput (b : Bool) : (C b).toScheme ⟶ pullback q t :=
  lift b ≫ arithmeticLastRetainedMiddleLocalOutput node data m j hj hm b

/-- Restriction preserves the whole original coefficient morphism, including nilpotents. -/
@[reassoc] theorem arithmeticLastRetainedMiddleSmoothOutput_base (b : Bool) :
    arithmeticLastRetainedMiddleSmoothOutput node data m j hj hm b ≫ pullback.fst q t =
      (C b).ι ≫ (A).ι ≫ pullback.fst f g' ≫ f := by
  rw [arithmeticLastRetainedMiddleSmoothOutput, Category.assoc,
    arithmeticLastRetainedMiddleLocalOutput_base,
    arithmeticLastRetainedMiddleSmoothLift_inclusion_assoc]

include hm in
/-- These actual two output charts cover every smooth last-retained/middle-terminal pair. -/
theorem arithmeticLastRetainedMiddleSmoothChart_covers
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (⨆ b, C b) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨b, z, hz⟩ := arithmeticLastRetainedMiddleLocal_exists
    node data m j hj hm hgen p.val p.property.1 p.property.2
  exact (le_iSup (fun b => C b) b) (show p ∈ C b from ⟨z, hz⟩)

/-- A genuine open cover of the whole smooth pair, with the two outputs constructed above. -/
def arithmeticLastRetainedMiddleSmoothCover
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (A).toScheme.OpenCover :=
  (A).toScheme.openCoverOfIsOpenCover C
    (arithmeticLastRetainedMiddleSmoothChart_covers node data m j hj hm hgen)

end FLT.Mazur.WeierstrassDividedDepth
