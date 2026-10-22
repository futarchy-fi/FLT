/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedOddLocalCover
public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedMiddleSmoothCover

/-!
# Actual local sources for the odd last-retained/terminal pair

Join the three unshifted normalized domains with both terminal incidence
sources. Each embeds openly in the original pair and retains its quotient output.
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


local notation "base" => finiteGlobalStructure hπ data (j + 1) hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
variable (hodd : depth = 2 * (j + 1) + 1) (hj0 : 0 < j)
local notation "X" => arithmeticLastRetainedOddLocalSource node data m j hj hodd hj0
local notation "inc" => arithmeticLastRetainedOddLocalInclusion node data m j hj hodd hj0
local notation "A" => arithmeticLastRetainedMiddlePairSmoothOpen node data m j hj

/-- Restrict each genuine local image to the original smooth-pair scheme. -/
def arithmeticLastRetainedOddSmoothChart (b : LastRetainedOddLocalIndex) : (A).toScheme.Opens :=
  (A).ι ⁻¹ᵁ (inc b).opensRange

local notation "C" => arithmeticLastRetainedOddSmoothChart node data m j hj hodd hj0

/-- Recover the complete original source from its open image. -/
def arithmeticLastRetainedOddSmoothLift (b : LastRetainedOddLocalIndex) : (C b).toScheme ⟶ X b :=
  ((A).ι ∣_ (inc b).opensRange) ≫ (inc b).isoOpensRange.inv

local notation "lift" => arithmeticLastRetainedOddSmoothLift node data m j hj hodd hj0

/-- Both entire original inputs are preserved by the restricted source lift. -/
@[reassoc] theorem arithmeticLastRetainedOddSmoothLift_inclusion (b : LastRetainedOddLocalIndex) :
    lift b ≫ inc b = (C b).ι ≫ (A).ι := by
  rw [arithmeticLastRetainedOddSmoothLift, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
  rfl

/-- Every smooth-pair chart carries its full constructed arithmetic quotient output. -/
def arithmeticLastRetainedOddSmoothOutput (b : LastRetainedOddLocalIndex) :
    (C b).toScheme ⟶ pullback q t :=
  lift b ≫ arithmeticLastRetainedOddLocalOutput node data m j hj hodd hj0 b

/-- Restriction preserves the whole original coefficient morphism, including nilpotents. -/
@[reassoc] theorem arithmeticLastRetainedOddSmoothOutput_base (b : LastRetainedOddLocalIndex) :
    arithmeticLastRetainedOddSmoothOutput node data m j hj hodd hj0 b ≫ pullback.fst q t =
      (C b).ι ≫ (A).ι ≫ pullback.fst f g' ≫ f := by
  rw [arithmeticLastRetainedOddSmoothOutput, Category.assoc,
    arithmeticLastRetainedOddLocalOutput_base,
    arithmeticLastRetainedOddSmoothLift_inclusion_assoc]

/-- These actual five output charts cover every smooth last-retained/odd-terminal pair. -/
theorem arithmeticLastRetainedOddSmoothChart_covers
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (⨆ b, C b) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨b, z, hz⟩ := arithmeticLastRetainedOddLocal_exists
    node data m j hj hodd hj0 hgen p.val p.property.1 p.property.2
  exact (le_iSup (fun b => C b) b) (show p ∈ C b from ⟨z, hz⟩)

/-- A genuine open cover of the whole smooth pair, with the five outputs constructed above. -/
def arithmeticLastRetainedOddSmoothCover
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (A).toScheme.OpenCover :=
  (A).toScheme.openCoverOfIsOpenCover C
    (arithmeticLastRetainedOddSmoothChart_covers node data m j hj hodd hj0 hgen)

end FLT.Mazur.WeierstrassDividedDepth
