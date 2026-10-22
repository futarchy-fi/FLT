/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedZeroSeparatedBoundarySmoothCover

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
local notation "out" => arithmeticLastRetainedZeroSeparatedBoundaryLocalOutput
  node data m j hk hj0 hdepth hnear
local notation "swap" => (pullbackSymmetry g f).hom

local instance arithmeticLastRetainedZeroSeparatedBoundaryReversedStructure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data k hk m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- Include the same actual local source with the original input order reversed. -/
def arithmeticLastRetainedZeroSeparatedBoundaryReversedInclusion
    (b : LastRetainedZeroSeparatedBoundaryLocalIndex) : X b ⟶ pullback g f :=
  inc b ≫ (pullbackSymmetry g f).inv

local notation "rev" => arithmeticLastRetainedZeroSeparatedBoundaryReversedInclusion
  node data m j hk hj0 hdepth hnear

/-- Reversing the input order preserves the open immersion of every local source. -/
instance arithmeticLastRetainedZeroSeparatedBoundaryReversedInclusion_isOpenImmersion
    (b : LastRetainedZeroSeparatedBoundaryLocalIndex) : IsOpenImmersion (rev b) := by
  dsimp only [arithmeticLastRetainedZeroSeparatedBoundaryReversedInclusion]
  infer_instance

/-- The same whole quotient output retains the first reversed coefficient morphism. -/
@[reassoc] theorem arithmeticLastRetainedZeroSeparatedBoundaryReversedOutput_base
    (b : LastRetainedZeroSeparatedBoundaryLocalIndex) :
    out b ≫ pullback.fst q t = rev b ≫ pullback.fst g f ≫ g := by
  rw [arithmeticLastRetainedZeroSeparatedBoundaryLocalOutput_base,
    arithmeticLastRetainedZeroSeparatedBoundaryReversedInclusion, Category.assoc,
    pullbackSymmetry_inv_comp_fst_assoc, pullback.condition]

/-- Every smooth reversed pair lies in one of the actual local-source images. -/
theorem arithmeticLastRetainedZeroSeparatedBoundaryReversedLocal_exists
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (p : (pullback g f : Scheme))
    (hs : chart d (pullback.fst g f p) ∈ (s).smoothLocus)
    (ht : chart c (pullback.snd g f p) ∈ (s).smoothLocus) :
    ∃ b, ∃ z : X b, rev b z = p := by
  have hfst : chart c (pullback.fst f g (swap p)) ∈ (s).smoothLocus := by
    rw [SchemePairSymmetryPoints.fst_apply]
    exact ht
  have hsnd : chart d (pullback.snd f g (swap p)) ∈ (s).smoothLocus := by
    rw [SchemePairSymmetryPoints.snd_apply]
    exact hs
  obtain ⟨b, z, hz⟩ := arithmeticLastRetainedZeroSeparatedBoundaryLocal_exists
    node data m j hk hj0 hdepth hnear hgen (swap p) hfst hsnd
  refine ⟨b, z, ?_⟩
  change (pullbackSymmetry g f).inv (inc b z) = p
  rw [hz]
  exact congrArg (fun morphism => morphism p) (Iso.hom_inv_id (pullbackSymmetry g f))

/-- The full original smooth domain with input order reversed. -/
def arithmeticLastRetainedZeroSeparatedBoundaryReversedSmoothOpen : (pullback g f).Opens :=
  (pullback.fst g f ≫ chart d) ⁻¹ᵁ (s).smoothLocus ⊓
    (pullback.snd g f ≫ chart c) ⁻¹ᵁ (s).smoothLocus

local notation "A" => arithmeticLastRetainedZeroSeparatedBoundaryReversedSmoothOpen node data m j hk

/-- Restrict each genuine source image to the full reversed smooth pair. -/
def arithmeticLastRetainedZeroSeparatedBoundaryReversedSmoothChart
    (b : LastRetainedZeroSeparatedBoundaryLocalIndex) : (A).toScheme.Opens :=
  (A).ι ⁻¹ᵁ (rev b).opensRange

local notation "C" => arithmeticLastRetainedZeroSeparatedBoundaryReversedSmoothChart
  node data m j hk hj0 hdepth hnear

/-- Recover the original source over the complete reversed smooth chart. -/
def arithmeticLastRetainedZeroSeparatedBoundaryReversedSmoothLift
    (b : LastRetainedZeroSeparatedBoundaryLocalIndex) : (C b).toScheme ⟶ X b :=
  ((A).ι ∣_ (rev b).opensRange) ≫ (rev b).isoOpensRange.inv

local notation "lift" => arithmeticLastRetainedZeroSeparatedBoundaryReversedSmoothLift
  node data m j hk hj0 hdepth hnear

/-- The lift retains both reversed inputs as whole scheme morphisms. -/
@[reassoc] theorem arithmeticLastRetainedZeroSeparatedBoundaryReversedSmoothLift_inclusion
    (b : LastRetainedZeroSeparatedBoundaryLocalIndex) :
    lift b ≫ rev b = (C b).ι ≫ (A).ι := by
  rw [arithmeticLastRetainedZeroSeparatedBoundaryReversedSmoothLift, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
  rfl

/-- The reversed smooth chart retains its whole quotient-valued output. -/
def arithmeticLastRetainedZeroSeparatedBoundaryReversedSmoothOutput
    (b : LastRetainedZeroSeparatedBoundaryLocalIndex) : (C b).toScheme ⟶ pullback q t :=
  lift b ≫ out b

/-- The output retains the coefficient morphism in reversed input order. -/
@[reassoc] theorem arithmeticLastRetainedZeroSeparatedBoundaryReversedSmoothOutput_base
    (b : LastRetainedZeroSeparatedBoundaryLocalIndex) :
    arithmeticLastRetainedZeroSeparatedBoundaryReversedSmoothOutput
      node data m j hk hj0 hdepth hnear b ≫ pullback.fst q t =
        (C b).ι ≫ (A).ι ≫ pullback.fst g f ≫ g := by
  rw [arithmeticLastRetainedZeroSeparatedBoundaryReversedSmoothOutput, Category.assoc,
    arithmeticLastRetainedZeroSeparatedBoundaryReversedOutput_base,
    arithmeticLastRetainedZeroSeparatedBoundaryReversedSmoothLift_inclusion_assoc]

/-- All smooth reversed pairs are covered, with no original coordinate puncture. -/
theorem arithmeticLastRetainedZeroSeparatedBoundaryReversedSmoothChart_covers
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (⨆ b, C b) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨b, z, hz⟩ := arithmeticLastRetainedZeroSeparatedBoundaryReversedLocal_exists
    node data m j hk hj0 hdepth hnear hgen p.val p.property.1 p.property.2
  exact (le_iSup (fun b => C b) b) (show p ∈ C b from ⟨z, hz⟩)

/-- A genuine open cover of the entire reversed smooth pair. -/
def arithmeticLastRetainedZeroSeparatedBoundaryReversedSmoothCover
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (A).toScheme.OpenCover :=
  (A).toScheme.openCoverOfIsOpenCover C
    (arithmeticLastRetainedZeroSeparatedBoundaryReversedSmoothChart_covers
      node data m j hk hj0 hdepth hnear hgen)

end FLT.Mazur.WeierstrassDividedDepth
