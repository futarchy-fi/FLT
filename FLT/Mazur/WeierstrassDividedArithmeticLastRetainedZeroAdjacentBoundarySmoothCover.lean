/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedZeroAdjacentBoundaryLocalCover

/-!
# Creation-zero adjacent boundary pairs at final stage two

At node depth four or five, combine the direct opposite formula, two self
formulas after the earlier transfer, and four complete last-transfer sources.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  arithmeticFixedAdjacentTargetCoordinates arithmeticTensorAtlasMap globalTensorAtlasObject
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m : ℕ) (hk : 2 ≤ n)
  (hdepth : 4 ≤ depth) (hnear : depth ≤ 5)
local notation "k" => 2
local notation "hi" => (Nat.le_refl 2)
local notation "hj" => (Nat.le_refl 2)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "ei" => data ⟨1, Nat.lt_succ_of_le ((Nat.le_trans
  (Nat.le_succ 1) hi).trans hk)⟩
local notation "ej" => data ⟨2, Nat.lt_succ_of_le hk⟩
local notation "c" => (Fin.succ ⟨k - 0,
  Nat.lt_succ_of_le ((Nat.sub_le k 0).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - 1,
  Nat.lt_succ_of_le ((Nat.sub_le k 1).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "I" => arithmeticFixedAdjacentSourceCoordinates hπ data m k hk 0 hi
local notation "J" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk 0 hj

local notation "u" => tensorCoord W (π ^ (0 + 0)) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2
local notation "v" => tensorCoord W (π ^ (0 + 1)) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 2

local notation "index" => fun r : ℕ => (Fin.succ ⟨k - r,
  Nat.lt_succ_of_le ((Nat.sub_le k r).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "f" => chart c ≫ s
local notation "g" => chart d ≫ s

local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

local notation "X" => arithmeticLastRetainedZeroAdjacentBoundaryLocalSource
  node data m hk hdepth hnear
local notation "inc" => arithmeticLastRetainedZeroAdjacentBoundaryLocalInclusion
  node data m hk hdepth hnear

local instance arithmeticLastRetainedZeroAdjacentBoundarySmoothCover_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data k hk m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- The unchanged pair open on which both original arithmetic inputs are smooth. -/
def arithmeticLastRetainedZeroAdjacentBoundarySmoothOpen : (pullback f g).Opens :=
  (pullback.fst f g ≫ chart c) ⁻¹ᵁ (s).smoothLocus ⊓
    (pullback.snd f g ≫ chart d) ⁻¹ᵁ (s).smoothLocus

local notation "A" => arithmeticLastRetainedZeroAdjacentBoundarySmoothOpen node data m hk

/-- Restrict the image of each actual local source to the smooth pair scheme. -/
def arithmeticLastRetainedZeroAdjacentBoundarySmoothChart
    (b : LastRetainedZeroAdjacentBoundaryLocalIndex) :
    (A).toScheme.Opens := (A).ι ⁻¹ᵁ (inc b).opensRange

local notation "C" => arithmeticLastRetainedZeroAdjacentBoundarySmoothChart
  node data m hk hdepth hnear

/-- The image-open inverse recovers the entire original local source. -/
def arithmeticLastRetainedZeroAdjacentBoundarySmoothLift
    (b : LastRetainedZeroAdjacentBoundaryLocalIndex) :
    (C b).toScheme ⟶ X b :=
  ((A).ι ∣_ (inc b).opensRange) ≫ (inc b).isoOpensRange.inv

local notation "lift" => arithmeticLastRetainedZeroAdjacentBoundarySmoothLift
  node data m hk hdepth hnear

/-- Both inputs are retained as a complete morphism to the original pair. -/
@[reassoc] theorem arithmeticLastRetainedZeroAdjacentBoundarySmoothLift_inclusion
    (b : LastRetainedZeroAdjacentBoundaryLocalIndex) :
    lift b ≫ inc b = (C b).ι ≫ (A).ι := by
  rw [arithmeticLastRetainedZeroAdjacentBoundarySmoothLift, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
  rfl

/-- The smooth-pair chart has the full previously constructed quotient output. -/
def arithmeticLastRetainedZeroAdjacentBoundarySmoothOutput
    (b : LastRetainedZeroAdjacentBoundaryLocalIndex) :
    (C b).toScheme ⟶ pullback q t :=
  lift b ≫ arithmeticLastRetainedZeroAdjacentBoundaryLocalOutput
    node data m hk hdepth hnear b

/-- The restricted output retains the first original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticLastRetainedZeroAdjacentBoundarySmoothOutput_base
    (b : LastRetainedZeroAdjacentBoundaryLocalIndex) :
    arithmeticLastRetainedZeroAdjacentBoundarySmoothOutput
      node data m hk hdepth hnear b ≫ pullback.fst q t =
        (C b).ι ≫ (A).ι ≫ pullback.fst f g ≫ f := by
  rw [arithmeticLastRetainedZeroAdjacentBoundarySmoothOutput, Category.assoc,
    arithmeticLastRetainedZeroAdjacentBoundaryLocalOutput_base,
    arithmeticLastRetainedZeroAdjacentBoundarySmoothLift_inclusion_assoc]

/-- Every smooth original pair lies in one actual restricted formula chart. -/
theorem arithmeticLastRetainedZeroAdjacentBoundarySmoothChart_covers
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (⨆ b, C b) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨b, z, hz⟩ := arithmeticLastRetainedZeroAdjacentBoundaryLocal_exists
    node data m hk hdepth hnear hgen p.val p.property.1 p.property.2
  exact (le_iSup (fun b => C b) b) (show p ∈ C b from ⟨z, hz⟩)

/-- An actual open cover of the entire smooth input pair, with local outputs above. -/
def arithmeticLastRetainedZeroAdjacentBoundarySmoothCover
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (A).toScheme.OpenCover :=
  (A).toScheme.openCoverOfIsOpenCover C
    (arithmeticLastRetainedZeroAdjacentBoundarySmoothChart_covers
      node data m hk hdepth hnear hgen)

end FLT.Mazur.WeierstrassDividedDepth
