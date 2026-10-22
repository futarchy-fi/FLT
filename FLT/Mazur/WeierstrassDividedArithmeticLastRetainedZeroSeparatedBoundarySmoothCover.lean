/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedZeroSeparatedBoundaryLocalCover

/-!
# Full local outputs for creation-zero/last-retained boundary pairs

Combine unshifted formulas, the earlier adjacent transfer, and the complete
last-transfer incidence cover. The latter also contains the double-zero case.
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
  (m j : ℕ) (hk : j + 2 ≤ n) (hj0 : 0 < j)
  (hdepth : 2 * (j + 2) ≤ depth) (hnear : depth ≤ 1 + 2 * (j + 2))
local notation "k" => j + 2
local notation "hi" => (Nat.le_add_left 2 j)
local notation "hj" => (Nat.le_refl (j + 2))
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "ei" => data ⟨1, Nat.lt_succ_of_le ((Nat.le_trans
  (Nat.le_succ 1) hi).trans hk)⟩
local notation "ej" => data ⟨j + 2, Nat.lt_succ_of_le hk⟩
local notation "c" => (Fin.succ ⟨k - 0,
  Nat.lt_succ_of_le ((Nat.sub_le k 0).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - (j + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (j + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "I" => arithmeticFixedAdjacentSourceCoordinates hπ data m k hk 0 hi
local notation "J" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk j hj

local notation "u" => tensorCoord W (π ^ (0 + 0)) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2
local notation "v" => tensorCoord W (π ^ (0 + (j + 1))) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 2

local notation "index" => fun r : ℕ => (Fin.succ ⟨k - r,
  Nat.lt_succ_of_le ((Nat.sub_le k r).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "f" => chart c ≫ s
local notation "g" => chart d ≫ s

local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

local notation "X" => arithmeticLastRetainedZeroSeparatedBoundaryLocalSource
  node data m j hk hj0 hdepth hnear
local notation "inc" => arithmeticLastRetainedZeroSeparatedBoundaryLocalInclusion
  node data m j hk hj0 hdepth hnear

local instance arithmeticLastRetainedZeroSeparatedBoundarySmoothCover_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data k hk m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- The unchanged pair open on which both original arithmetic inputs are smooth. -/
def arithmeticLastRetainedZeroSeparatedBoundarySmoothOpen : (pullback f g).Opens :=
  (pullback.fst f g ≫ chart c) ⁻¹ᵁ (s).smoothLocus ⊓
    (pullback.snd f g ≫ chart d) ⁻¹ᵁ (s).smoothLocus

local notation "A" => arithmeticLastRetainedZeroSeparatedBoundarySmoothOpen node data m j hk

/-- Restrict the image of each actual local source to the smooth pair scheme. -/
def arithmeticLastRetainedZeroSeparatedBoundarySmoothChart
    (b : LastRetainedZeroSeparatedBoundaryLocalIndex) :
    (A).toScheme.Opens := (A).ι ⁻¹ᵁ (inc b).opensRange

local notation "C" => arithmeticLastRetainedZeroSeparatedBoundarySmoothChart
  node data m j hk hj0 hdepth hnear

/-- The image-open inverse recovers the entire original local source. -/
def arithmeticLastRetainedZeroSeparatedBoundarySmoothLift
    (b : LastRetainedZeroSeparatedBoundaryLocalIndex) :
    (C b).toScheme ⟶ X b :=
  ((A).ι ∣_ (inc b).opensRange) ≫ (inc b).isoOpensRange.inv

local notation "lift" => arithmeticLastRetainedZeroSeparatedBoundarySmoothLift
  node data m j hk hj0 hdepth hnear

/-- Both inputs are retained as a complete morphism to the original pair. -/
@[reassoc] theorem arithmeticLastRetainedZeroSeparatedBoundarySmoothLift_inclusion
    (b : LastRetainedZeroSeparatedBoundaryLocalIndex) :
    lift b ≫ inc b = (C b).ι ≫ (A).ι := by
  rw [arithmeticLastRetainedZeroSeparatedBoundarySmoothLift, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
  rfl

/-- The smooth-pair chart has the full previously constructed quotient output. -/
def arithmeticLastRetainedZeroSeparatedBoundarySmoothOutput
    (b : LastRetainedZeroSeparatedBoundaryLocalIndex) :
    (C b).toScheme ⟶ pullback q t :=
  lift b ≫ arithmeticLastRetainedZeroSeparatedBoundaryLocalOutput
    node data m j hk hj0 hdepth hnear b

/-- The restricted output retains the first original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticLastRetainedZeroSeparatedBoundarySmoothOutput_base
    (b : LastRetainedZeroSeparatedBoundaryLocalIndex) :
    arithmeticLastRetainedZeroSeparatedBoundarySmoothOutput
      node data m j hk hj0 hdepth hnear b ≫ pullback.fst q t =
        (C b).ι ≫ (A).ι ≫ pullback.fst f g ≫ f := by
  rw [arithmeticLastRetainedZeroSeparatedBoundarySmoothOutput, Category.assoc,
    arithmeticLastRetainedZeroSeparatedBoundaryLocalOutput_base,
    arithmeticLastRetainedZeroSeparatedBoundarySmoothLift_inclusion_assoc]

/-- Every smooth original pair lies in one actual restricted formula chart. -/
theorem arithmeticLastRetainedZeroSeparatedBoundarySmoothChart_covers
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (⨆ b, C b) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨b, z, hz⟩ := arithmeticLastRetainedZeroSeparatedBoundaryLocal_exists
    node data m j hk hj0 hdepth hnear hgen p.val p.property.1 p.property.2
  exact (le_iSup (fun b => C b) b) (show p ∈ C b from ⟨z, hz⟩)

/-- An actual open cover of the entire smooth input pair, with local outputs above. -/
def arithmeticLastRetainedZeroSeparatedBoundarySmoothCover
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (A).toScheme.OpenCover :=
  (A).toScheme.openCoverOfIsOpenCover C
    (arithmeticLastRetainedZeroSeparatedBoundarySmoothChart_covers
      node data m j hk hj0 hdepth hnear hgen)

end FLT.Mazur.WeierstrassDividedDepth
