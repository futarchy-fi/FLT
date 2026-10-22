/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedAdjacentFlexiblePreMiddleLocalCover

/-!
# Flexible adjacent retained-pair smoothcover

Cover the full smooth pair through actual unshifted and transferred domains.
Each target chooses its sum-depth or reflected formula, with the output stage
bounded by the maximum of the three actual smaller sum/reflected depths.
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
  (m k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i + 2 ≤ k)
  (hiNext : (i + 1) + 2 ≤ k) (hiLast : ((i + 1) + 1) + 2 ≤ k)
  (hpre : 2 * ((i + 1) + 2) < depth)
  (hstage : max (min (2 * i + 3) (depth - (2 * i + 3)))
    (max (min (2 * i + 4) (depth - (2 * i + 4)))
      (min (2 * i + 5) (depth - (2 * i + 5)))) ≤ k)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "ei" => data ⟨i + 2, Nat.lt_succ_of_le (hi.trans hk)⟩
local notation "ej" => data ⟨(i + 1) + 2, Nat.lt_succ_of_le (hiNext.trans hk)⟩
local notation "c" => (Fin.succ ⟨k - (i + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (i + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - ((i + 1) + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k ((i + 1) + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "I" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk i hi
local notation "J" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk (i + 1) hiNext

local notation "di" => data ⟨i + 1, by omega⟩
local notation "dj" => data ⟨(i + 1) + 1, by omega⟩
local notation "u" => tensorCoord W (π ^ (0 + (i + 1))) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2
local notation "v" => tensorCoord W (π ^ (0 + ((i + 1) + 1))) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 2

local notation "index" => fun r : ℕ => (Fin.succ ⟨k - r,
  Nat.lt_succ_of_le ((Nat.sub_le k r).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "f" => chart c ≫ s
local notation "g" => chart d ≫ s

local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

local notation "X" => arithmeticRetainedAdjacentFlexiblePreMiddleLocalSource
  node data m k hk i hi hiNext hiLast hpre hstage
local notation "inc" => arithmeticRetainedAdjacentFlexiblePreMiddleLocalInclusion
  node data m k hk i hi hiNext hiLast hpre hstage

local instance arithmeticAdjacentFlexiblePreMiddleSmoothCover_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data k hk m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- The unchanged pair open on which both original arithmetic inputs are smooth. -/
def arithmeticRetainedAdjacentFlexiblePreMiddleSmoothOpen : (pullback f g).Opens :=
  (pullback.fst f g ≫ chart c) ⁻¹ᵁ (s).smoothLocus ⊓
    (pullback.snd f g ≫ chart d) ⁻¹ᵁ (s).smoothLocus

local notation "A" => arithmeticRetainedAdjacentFlexiblePreMiddleSmoothOpen node data m k hk i

/-- Restrict the image of each actual local source to the smooth pair scheme. -/
def arithmeticRetainedAdjacentFlexiblePreMiddleSmoothChart
    (b : RetainedAdjacentFlexiblePreMiddleLocalIndex) :
    (A).toScheme.Opens := (A).ι ⁻¹ᵁ (inc b).opensRange

local notation "C" => arithmeticRetainedAdjacentFlexiblePreMiddleSmoothChart
  node data m k hk i hi hiNext hiLast hpre hstage

/-- The image-open inverse recovers the entire original local source. -/
def arithmeticRetainedAdjacentFlexiblePreMiddleSmoothLift
    (b : RetainedAdjacentFlexiblePreMiddleLocalIndex) :
    (C b).toScheme ⟶ X b :=
  ((A).ι ∣_ (inc b).opensRange) ≫ (inc b).isoOpensRange.inv

local notation "lift" => arithmeticRetainedAdjacentFlexiblePreMiddleSmoothLift
  node data m k hk i hi hiNext hiLast hpre hstage

/-- Both inputs are retained as a complete morphism to the original pair. -/
@[reassoc] theorem arithmeticRetainedAdjacentFlexiblePreMiddleSmoothLift_inclusion
    (b : RetainedAdjacentFlexiblePreMiddleLocalIndex) :
    lift b ≫ inc b = (C b).ι ≫ (A).ι := by
  rw [arithmeticRetainedAdjacentFlexiblePreMiddleSmoothLift, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
  rfl

/-- The smooth-pair chart has the full previously constructed quotient output. -/
def arithmeticRetainedAdjacentFlexiblePreMiddleSmoothOutput
    (b : RetainedAdjacentFlexiblePreMiddleLocalIndex) :
    (C b).toScheme ⟶ pullback q t :=
  lift b ≫ arithmeticRetainedAdjacentFlexiblePreMiddleLocalOutput
    node data m k hk i hi hiNext hiLast hpre hstage b

/-- The restricted output retains the first original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticRetainedAdjacentFlexiblePreMiddleSmoothOutput_base
    (b : RetainedAdjacentFlexiblePreMiddleLocalIndex) :
    arithmeticRetainedAdjacentFlexiblePreMiddleSmoothOutput
      node data m k hk i hi hiNext hiLast hpre hstage b ≫ pullback.fst q t =
        (C b).ι ≫ (A).ι ≫ pullback.fst f g ≫ f := by
  rw [arithmeticRetainedAdjacentFlexiblePreMiddleSmoothOutput, Category.assoc,
    arithmeticRetainedAdjacentFlexiblePreMiddleLocalOutput_base,
    arithmeticRetainedAdjacentFlexiblePreMiddleSmoothLift_inclusion_assoc]

/-- Every smooth original pair lies in one actual restricted formula chart. -/
theorem arithmeticRetainedAdjacentFlexiblePreMiddleSmoothChart_covers
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (⨆ b, C b) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨b, z, hz⟩ := arithmeticRetainedAdjacentFlexiblePreMiddleLocal_exists
    node data m k hk i hi hiNext hiLast hpre hstage hgen p.val p.property.1 p.property.2
  exact (le_iSup (fun b => C b) b) (show p ∈ C b from ⟨z, hz⟩)

/-- An actual open cover of the entire smooth input pair, with local outputs above. -/
def arithmeticRetainedAdjacentFlexiblePreMiddleSmoothCover
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (A).toScheme.OpenCover :=
  (A).toScheme.openCoverOfIsOpenCover C
    (arithmeticRetainedAdjacentFlexiblePreMiddleSmoothChart_covers
      node data m k hk i hi hiNext hiLast hpre hstage hgen)

end FLT.Mazur.WeierstrassDividedDepth
