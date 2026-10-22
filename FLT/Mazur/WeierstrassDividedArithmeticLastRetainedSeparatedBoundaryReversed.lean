/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedSeparatedBoundarySmoothCover

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
local notation "out" => arithmeticLastRetainedSeparatedBoundaryLocalOutput
  node data m i j hk hgap hdepth hnear hstage
local notation "swap" => (pullbackSymmetry g f).hom

local instance arithmeticLastRetainedSeparatedBoundaryReversedStructure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data k hk m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- Include the same actual local source with the original input order reversed. -/
def arithmeticLastRetainedSeparatedBoundaryReversedInclusion
    (b : LastRetainedSeparatedBoundaryLocalIndex) : X b ⟶ pullback g f :=
  inc b ≫ (pullbackSymmetry g f).inv

local notation "rev" => arithmeticLastRetainedSeparatedBoundaryReversedInclusion
  node data m i j hk hgap hdepth hnear hstage

/-- Reversing the input order preserves the open immersion of every local source. -/
instance arithmeticLastRetainedSeparatedBoundaryReversedInclusion_isOpenImmersion
    (b : LastRetainedSeparatedBoundaryLocalIndex) : IsOpenImmersion (rev b) := by
  dsimp only [arithmeticLastRetainedSeparatedBoundaryReversedInclusion]
  infer_instance

/-- The same whole quotient output retains the first reversed coefficient morphism. -/
@[reassoc] theorem arithmeticLastRetainedSeparatedBoundaryReversedOutput_base
    (b : LastRetainedSeparatedBoundaryLocalIndex) :
    out b ≫ pullback.fst q t = rev b ≫ pullback.fst g f ≫ g := by
  rw [arithmeticLastRetainedSeparatedBoundaryLocalOutput_base,
    arithmeticLastRetainedSeparatedBoundaryReversedInclusion, Category.assoc,
    pullbackSymmetry_inv_comp_fst_assoc, pullback.condition]

/-- Every smooth reversed pair lies in one of the actual local-source images. -/
theorem arithmeticLastRetainedSeparatedBoundaryReversedLocal_exists
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
  obtain ⟨b, z, hz⟩ := arithmeticLastRetainedSeparatedBoundaryLocal_exists
    node data m i j hk hgap hdepth hnear hstage hgen (swap p) hfst hsnd
  refine ⟨b, z, ?_⟩
  change (pullbackSymmetry g f).inv (inc b z) = p
  rw [hz]
  exact congrArg (fun morphism => morphism p) (Iso.hom_inv_id (pullbackSymmetry g f))

/-- The full original smooth domain with input order reversed. -/
def arithmeticLastRetainedSeparatedBoundaryReversedSmoothOpen : (pullback g f).Opens :=
  (pullback.fst g f ≫ chart d) ⁻¹ᵁ (s).smoothLocus ⊓
    (pullback.snd g f ≫ chart c) ⁻¹ᵁ (s).smoothLocus

local notation "A" => arithmeticLastRetainedSeparatedBoundaryReversedSmoothOpen node data m i j hk

/-- Restrict each genuine source image to the full reversed smooth pair. -/
def arithmeticLastRetainedSeparatedBoundaryReversedSmoothChart
    (b : LastRetainedSeparatedBoundaryLocalIndex) : (A).toScheme.Opens :=
  (A).ι ⁻¹ᵁ (rev b).opensRange

local notation "C" => arithmeticLastRetainedSeparatedBoundaryReversedSmoothChart
  node data m i j hk hgap hdepth hnear hstage

/-- Recover the original source over the complete reversed smooth chart. -/
def arithmeticLastRetainedSeparatedBoundaryReversedSmoothLift
    (b : LastRetainedSeparatedBoundaryLocalIndex) : (C b).toScheme ⟶ X b :=
  ((A).ι ∣_ (rev b).opensRange) ≫ (rev b).isoOpensRange.inv

local notation "lift" => arithmeticLastRetainedSeparatedBoundaryReversedSmoothLift
  node data m i j hk hgap hdepth hnear hstage

/-- The lift retains both reversed inputs as whole scheme morphisms. -/
@[reassoc] theorem arithmeticLastRetainedSeparatedBoundaryReversedSmoothLift_inclusion
    (b : LastRetainedSeparatedBoundaryLocalIndex) :
    lift b ≫ rev b = (C b).ι ≫ (A).ι := by
  rw [arithmeticLastRetainedSeparatedBoundaryReversedSmoothLift, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
  rfl

/-- The reversed smooth chart retains its whole quotient-valued output. -/
def arithmeticLastRetainedSeparatedBoundaryReversedSmoothOutput
    (b : LastRetainedSeparatedBoundaryLocalIndex) : (C b).toScheme ⟶ pullback q t :=
  lift b ≫ out b

/-- The output retains the coefficient morphism in reversed input order. -/
@[reassoc] theorem arithmeticLastRetainedSeparatedBoundaryReversedSmoothOutput_base
    (b : LastRetainedSeparatedBoundaryLocalIndex) :
    arithmeticLastRetainedSeparatedBoundaryReversedSmoothOutput
      node data m i j hk hgap hdepth hnear hstage b ≫ pullback.fst q t =
        (C b).ι ≫ (A).ι ≫ pullback.fst g f ≫ g := by
  rw [arithmeticLastRetainedSeparatedBoundaryReversedSmoothOutput, Category.assoc,
    arithmeticLastRetainedSeparatedBoundaryReversedOutput_base,
    arithmeticLastRetainedSeparatedBoundaryReversedSmoothLift_inclusion_assoc]

/-- All smooth reversed pairs are covered, with no original coordinate puncture. -/
theorem arithmeticLastRetainedSeparatedBoundaryReversedSmoothChart_covers
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (⨆ b, C b) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨b, z, hz⟩ := arithmeticLastRetainedSeparatedBoundaryReversedLocal_exists
    node data m i j hk hgap hdepth hnear hstage hgen p.val p.property.1 p.property.2
  exact (le_iSup (fun b => C b) b) (show p ∈ C b from ⟨z, hz⟩)

/-- A genuine open cover of the entire reversed smooth pair. -/
def arithmeticLastRetainedSeparatedBoundaryReversedSmoothCover
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (A).toScheme.OpenCover :=
  (A).toScheme.openCoverOfIsOpenCover C
    (arithmeticLastRetainedSeparatedBoundaryReversedSmoothChart_covers
      node data m i j hk hgap hdepth hnear hstage hgen)

end FLT.Mazur.WeierstrassDividedDepth
