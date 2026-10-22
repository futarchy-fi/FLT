/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedSeparatedBoundaryLocalCover

/-!
# Full local outputs for separated last-retained boundary pairs

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
  arithmeticFixedAdjacentTargetCoordinates
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m i j : ℕ) (hk : j + 2 ≤ n) (hgap : i + 1 < j)
  (hdepth : 2 * (j + 2) ≤ depth) (hnear : depth ≤ (i + 1) + 2 * (j + 2))
  (hstage : max (min (i + j + 2) (depth - (i + j + 2)))
    (min (i + j + 3) (depth - (i + j + 3))) ≤ j + 2)
local notation "k" => j + 2
local notation "hi" => (by omega : i + 2 ≤ k)
local notation "hj" => (by omega : j + 2 ≤ k)
local notation "hiNext" => (by omega : (i + 1) + 2 ≤ k)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "ei" => data ⟨i + 2, Nat.lt_succ_of_le ((hi).trans hk)⟩
local notation "ej" => data ⟨j + 2, Nat.lt_succ_of_le ((hj).trans hk)⟩
local notation "c" => (Fin.succ ⟨k - (i + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (i + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - (j + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (j + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "I" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk i hi
local notation "J" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk j hj

local notation "di" => data ⟨i + 1, by omega⟩
local notation "dj" => data ⟨j + 1, by omega⟩
local notation "u" => tensorCoord W (π ^ (0 + (i + 1))) π
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

local notation "X" => arithmeticLastRetainedSeparatedBoundaryLocalSource
  node data m i j hk hgap hdepth hnear hstage
local notation "inc" => arithmeticLastRetainedSeparatedBoundaryLocalInclusion
  node data m i j hk hgap hdepth hnear hstage

local instance arithmeticLastRetainedSeparatedBoundarySmoothCover_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data k hk m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- The unchanged pair open on which both original arithmetic inputs are smooth. -/
def arithmeticLastRetainedSeparatedBoundarySmoothOpen : (pullback f g).Opens :=
  (pullback.fst f g ≫ chart c) ⁻¹ᵁ (s).smoothLocus ⊓
    (pullback.snd f g ≫ chart d) ⁻¹ᵁ (s).smoothLocus

local notation "A" => arithmeticLastRetainedSeparatedBoundarySmoothOpen node data m i j hk

/-- Restrict the image of each actual local source to the smooth pair scheme. -/
def arithmeticLastRetainedSeparatedBoundarySmoothChart
    (b : LastRetainedSeparatedBoundaryLocalIndex) :
    (A).toScheme.Opens := (A).ι ⁻¹ᵁ (inc b).opensRange

local notation "C" => arithmeticLastRetainedSeparatedBoundarySmoothChart
  node data m i j hk hgap hdepth hnear hstage

/-- The image-open inverse recovers the entire original local source. -/
def arithmeticLastRetainedSeparatedBoundarySmoothLift
    (b : LastRetainedSeparatedBoundaryLocalIndex) :
    (C b).toScheme ⟶ X b :=
  ((A).ι ∣_ (inc b).opensRange) ≫ (inc b).isoOpensRange.inv

local notation "lift" => arithmeticLastRetainedSeparatedBoundarySmoothLift
  node data m i j hk hgap hdepth hnear hstage

/-- Both inputs are retained as a complete morphism to the original pair. -/
@[reassoc] theorem arithmeticLastRetainedSeparatedBoundarySmoothLift_inclusion
    (b : LastRetainedSeparatedBoundaryLocalIndex) :
    lift b ≫ inc b = (C b).ι ≫ (A).ι := by
  rw [arithmeticLastRetainedSeparatedBoundarySmoothLift, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
  rfl

/-- The smooth-pair chart has the full previously constructed quotient output. -/
def arithmeticLastRetainedSeparatedBoundarySmoothOutput
    (b : LastRetainedSeparatedBoundaryLocalIndex) :
    (C b).toScheme ⟶ pullback q t :=
  lift b ≫ arithmeticLastRetainedSeparatedBoundaryLocalOutput
    node data m i j hk hgap hdepth hnear hstage b

/-- The restricted output retains the first original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticLastRetainedSeparatedBoundarySmoothOutput_base
    (b : LastRetainedSeparatedBoundaryLocalIndex) :
    arithmeticLastRetainedSeparatedBoundarySmoothOutput
      node data m i j hk hgap hdepth hnear hstage b ≫ pullback.fst q t =
        (C b).ι ≫ (A).ι ≫ pullback.fst f g ≫ f := by
  rw [arithmeticLastRetainedSeparatedBoundarySmoothOutput, Category.assoc,
    arithmeticLastRetainedSeparatedBoundaryLocalOutput_base,
    arithmeticLastRetainedSeparatedBoundarySmoothLift_inclusion_assoc]

/-- Every smooth original pair lies in one actual restricted formula chart. -/
theorem arithmeticLastRetainedSeparatedBoundarySmoothChart_covers
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (⨆ b, C b) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨b, z, hz⟩ := arithmeticLastRetainedSeparatedBoundaryLocal_exists
    node data m i j hk hgap hdepth hnear hstage hgen p.val p.property.1 p.property.2
  exact (le_iSup (fun b => C b) b) (show p ∈ C b from ⟨z, hz⟩)

/-- An actual open cover of the entire smooth input pair, with local outputs above. -/
def arithmeticLastRetainedSeparatedBoundarySmoothCover
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (A).toScheme.OpenCover :=
  (A).toScheme.openCoverOfIsOpenCover C
    (arithmeticLastRetainedSeparatedBoundarySmoothChart_covers
      node data m i j hk hgap hdepth hnear hstage hgen)

end FLT.Mazur.WeierstrassDividedDepth
