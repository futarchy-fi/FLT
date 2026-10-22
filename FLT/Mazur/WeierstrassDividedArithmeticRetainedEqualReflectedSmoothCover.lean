/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedEqualReflectedLocalCover

/-!
# An actual smooth-pair open cover with reflected local outputs

Restrict all ten source images to the open where both original inputs are
smooth. Each restriction retains its entire quotient-valued output, and the
images cover the whole smooth pair scheme. No overlap equality is assumed.
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
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i + 2 ≤ k) (hiNext : (i + 1) + 2 ≤ k)
  (hlo : 2 * (i + 2) < depth) (hhi : depth ≤ (i + 1) + 2 * (i + 2))
  (hstage : depth - 2 * (i + 1) ≤ k)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "e" => data ⟨i + 2, Nat.lt_succ_of_le (hi.trans hk)⟩
local notation "c" => (Fin.succ ⟨k - (i + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (i + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - ((i + 1) + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k ((i + 1) + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "f" => chart c ≫ s
local notation "g" => chart d ≫ s
local notation "I" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk i hi
local notation "u" => tensorCoord W (π ^ (0 + (i + 1))) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 2
local notation "V" => arithmeticTargetSelfFlexiblePreMiddleOpen node data m k hk i hi
  (by omega) (by omega)
local notation "Z" => arithmeticTargetSelfReciprocalOpen node data m k hk i hi
local notation "O" => arithmeticFixedAdjacentPairOpen hπ data m k hk (i + 1) hiNext f
local notation "D" => arithmeticRetainedDoubleOpen hπ data m k hk
  (i + 1) (i + 1) hiNext hiNext
local notation "MC" => arithmeticRetainedSelfReflectedMixedChart node data m k hk i hi hiNext
  (by omega) (by omega) (by omega)
local notation "MO" => arithmeticRetainedSelfReflectedMixedOutput node data m k hk i hi hiNext
  (by omega) (by omega) (by omega)
local notation "TC" => arithmeticRetainedSelfFlexiblePreMiddleTransferChart node data m k hk
  (i + 1) hiNext (by omega) (by omega)
local notation "TO" => arithmeticRetainedSelfFlexiblePreMiddleTransferOutput node data m k hk
  (i + 1) hiNext (by omega) (by omega)
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

local notation "X" => arithmeticRetainedEqualReflectedLocalSource node data m k hk i hi hiNext
  hlo hhi hstage
local notation "inc" => arithmeticRetainedEqualReflectedLocalInclusion node data m k hk i hi hiNext
  hlo hhi hstage

local instance arithmeticEqualReflectedSmoothCover_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data k hk m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- The unchanged pair open on which both original arithmetic inputs are smooth. -/
def arithmeticRetainedEqualReflectedSmoothOpen : (pullback f f).Opens :=
  (pullback.fst f f ≫ chart c) ⁻¹ᵁ (s).smoothLocus ⊓
    (pullback.snd f f ≫ chart c) ⁻¹ᵁ (s).smoothLocus

local notation "A" => arithmeticRetainedEqualReflectedSmoothOpen node data m k hk i

/-- Restrict the image of each actual local source to the smooth pair scheme. -/
def arithmeticRetainedEqualReflectedSmoothChart (b : RetainedEqualReflectedLocalIndex) :
    (A).toScheme.Opens := (A).ι ⁻¹ᵁ (inc b).opensRange

local notation "C" => arithmeticRetainedEqualReflectedSmoothChart
  node data m k hk i hi hiNext hlo hhi hstage

/-- The image-open inverse recovers the entire original local source. -/
def arithmeticRetainedEqualReflectedSmoothLift (b : RetainedEqualReflectedLocalIndex) :
    (C b).toScheme ⟶ X b :=
  ((A).ι ∣_ (inc b).opensRange) ≫ (inc b).isoOpensRange.inv

local notation "lift" => arithmeticRetainedEqualReflectedSmoothLift
  node data m k hk i hi hiNext hlo hhi hstage

/-- Both inputs are retained as a complete morphism to the original pair. -/
@[reassoc] theorem arithmeticRetainedEqualReflectedSmoothLift_inclusion
    (b : RetainedEqualReflectedLocalIndex) :
    lift b ≫ inc b = (C b).ι ≫ (A).ι := by
  rw [arithmeticRetainedEqualReflectedSmoothLift, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
  rfl

/-- The smooth-pair chart has the full previously constructed quotient output. -/
def arithmeticRetainedEqualReflectedSmoothOutput (b : RetainedEqualReflectedLocalIndex) :
    (C b).toScheme ⟶ pullback q t :=
  lift b ≫ arithmeticRetainedEqualReflectedLocalOutput
    node data m k hk i hi hiNext hlo hhi hstage b

/-- The restricted output retains the first original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticRetainedEqualReflectedSmoothOutput_base
    (b : RetainedEqualReflectedLocalIndex) :
    arithmeticRetainedEqualReflectedSmoothOutput node data m k hk i hi hiNext
      hlo hhi hstage b ≫ pullback.fst q t =
        (C b).ι ≫ (A).ι ≫ pullback.fst f f ≫ f := by
  rw [arithmeticRetainedEqualReflectedSmoothOutput, Category.assoc,
    arithmeticRetainedEqualReflectedLocalOutput_base,
    arithmeticRetainedEqualReflectedSmoothLift_inclusion_assoc]

/-- Every smooth original pair lies in one actual restricted formula chart. -/
theorem arithmeticRetainedEqualReflectedSmoothChart_covers
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (⨆ b, C b) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨b, z, hz⟩ := arithmeticRetainedEqualReflectedLocal_exists
    node data m k hk i hi hiNext hlo hhi hstage hgen p.val p.property.1 p.property.2
  exact (le_iSup (fun b => C b) b) (show p ∈ C b from ⟨z, hz⟩)

/-- An actual open cover of the entire smooth input pair, with local outputs above. -/
def arithmeticRetainedEqualReflectedSmoothCover
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (A).toScheme.OpenCover :=
  (A).toScheme.openCoverOfIsOpenCover C
    (arithmeticRetainedEqualReflectedSmoothChart_covers
      node data m k hk i hi hiNext hlo hhi hstage hgen)

end FLT.Mazur.WeierstrassDividedDepth
