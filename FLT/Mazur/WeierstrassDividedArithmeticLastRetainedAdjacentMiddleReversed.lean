/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedAdjacentMiddleSmoothCover

/-!
# Full local outputs for adjacent last-retained middle pairs

Combine unshifted formulas, the full self cover after transfer, and the complete
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
  (m i : ℕ) (hk : i + 3 ≤ n) (hmiddle : 2 * (i + 3) = depth)
local notation "j" => i + 1
local notation "k" => i + 3
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

local notation "X" => arithmeticLastRetainedAdjacentMiddleLocalSource
  node data m i hk hmiddle
local notation "inc" => arithmeticLastRetainedAdjacentMiddleLocalInclusion
  node data m i hk hmiddle
local notation "out" => arithmeticLastRetainedAdjacentMiddleLocalOutput
  node data m i hk hmiddle
local notation "swap" => (pullbackSymmetry g f).hom

local instance arithmeticLastRetainedAdjacentMiddleReversedStructure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data k hk m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- Include the same actual local source with the original input order reversed. -/
def arithmeticLastRetainedAdjacentMiddleReversedInclusion
    (b : LastRetainedAdjacentMiddleLocalIndex) : X b ⟶ pullback g f :=
  inc b ≫ (pullbackSymmetry g f).inv

local notation "rev" => arithmeticLastRetainedAdjacentMiddleReversedInclusion
  node data m i hk hmiddle

/-- Reversing the input order preserves the open immersion of every local source. -/
instance arithmeticLastRetainedAdjacentMiddleReversedInclusion_isOpenImmersion
    (b : LastRetainedAdjacentMiddleLocalIndex) : IsOpenImmersion (rev b) := by
  dsimp only [arithmeticLastRetainedAdjacentMiddleReversedInclusion]
  infer_instance

/-- The same whole quotient output retains the first reversed coefficient morphism. -/
@[reassoc] theorem arithmeticLastRetainedAdjacentMiddleReversedOutput_base
    (b : LastRetainedAdjacentMiddleLocalIndex) :
    out b ≫ pullback.fst q t = rev b ≫ pullback.fst g f ≫ g := by
  rw [arithmeticLastRetainedAdjacentMiddleLocalOutput_base,
    arithmeticLastRetainedAdjacentMiddleReversedInclusion, Category.assoc,
    pullbackSymmetry_inv_comp_fst_assoc, pullback.condition]

/-- Every smooth reversed pair lies in one of the actual local-source images. -/
theorem arithmeticLastRetainedAdjacentMiddleReversedLocal_exists
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
  obtain ⟨b, z, hz⟩ := arithmeticLastRetainedAdjacentMiddleLocal_exists
    node data m i hk hmiddle hgen (swap p) hfst hsnd
  refine ⟨b, z, ?_⟩
  change (pullbackSymmetry g f).inv (inc b z) = p
  rw [hz]
  exact congrArg (fun morphism => morphism p) (Iso.hom_inv_id (pullbackSymmetry g f))

/-- The full original smooth domain with input order reversed. -/
def arithmeticLastRetainedAdjacentMiddleReversedSmoothOpen : (pullback g f).Opens :=
  (pullback.fst g f ≫ chart d) ⁻¹ᵁ (s).smoothLocus ⊓
    (pullback.snd g f ≫ chart c) ⁻¹ᵁ (s).smoothLocus

local notation "A" => arithmeticLastRetainedAdjacentMiddleReversedSmoothOpen node data m i hk

/-- Restrict each genuine source image to the full reversed smooth pair. -/
def arithmeticLastRetainedAdjacentMiddleReversedSmoothChart
    (b : LastRetainedAdjacentMiddleLocalIndex) : (A).toScheme.Opens :=
  (A).ι ⁻¹ᵁ (rev b).opensRange

local notation "C" => arithmeticLastRetainedAdjacentMiddleReversedSmoothChart
  node data m i hk hmiddle

/-- Recover the original source over the complete reversed smooth chart. -/
def arithmeticLastRetainedAdjacentMiddleReversedSmoothLift
    (b : LastRetainedAdjacentMiddleLocalIndex) : (C b).toScheme ⟶ X b :=
  ((A).ι ∣_ (rev b).opensRange) ≫ (rev b).isoOpensRange.inv

local notation "lift" => arithmeticLastRetainedAdjacentMiddleReversedSmoothLift
  node data m i hk hmiddle

/-- The lift retains both reversed inputs as whole scheme morphisms. -/
@[reassoc] theorem arithmeticLastRetainedAdjacentMiddleReversedSmoothLift_inclusion
    (b : LastRetainedAdjacentMiddleLocalIndex) :
    lift b ≫ rev b = (C b).ι ≫ (A).ι := by
  rw [arithmeticLastRetainedAdjacentMiddleReversedSmoothLift, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
  rfl

/-- The reversed smooth chart retains its whole quotient-valued output. -/
def arithmeticLastRetainedAdjacentMiddleReversedSmoothOutput
    (b : LastRetainedAdjacentMiddleLocalIndex) : (C b).toScheme ⟶ pullback q t :=
  lift b ≫ out b

/-- The output retains the coefficient morphism in reversed input order. -/
@[reassoc] theorem arithmeticLastRetainedAdjacentMiddleReversedSmoothOutput_base
    (b : LastRetainedAdjacentMiddleLocalIndex) :
    arithmeticLastRetainedAdjacentMiddleReversedSmoothOutput
      node data m i hk hmiddle b ≫ pullback.fst q t =
        (C b).ι ≫ (A).ι ≫ pullback.fst g f ≫ g := by
  rw [arithmeticLastRetainedAdjacentMiddleReversedSmoothOutput, Category.assoc,
    arithmeticLastRetainedAdjacentMiddleReversedOutput_base,
    arithmeticLastRetainedAdjacentMiddleReversedSmoothLift_inclusion_assoc]

/-- All smooth reversed pairs are covered, with no original coordinate puncture. -/
theorem arithmeticLastRetainedAdjacentMiddleReversedSmoothChart_covers
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (⨆ b, C b) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨b, z, hz⟩ := arithmeticLastRetainedAdjacentMiddleReversedLocal_exists
    node data m i hk hmiddle hgen p.val p.property.1 p.property.2
  exact (le_iSup (fun b => C b) b) (show p ∈ C b from ⟨z, hz⟩)

/-- A genuine open cover of the entire reversed smooth pair. -/
def arithmeticLastRetainedAdjacentMiddleReversedSmoothCover
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (A).toScheme.OpenCover :=
  (A).toScheme.openCoverOfIsOpenCover C
    (arithmeticLastRetainedAdjacentMiddleReversedSmoothChart_covers
      node data m i hk hmiddle hgen)

end FLT.Mazur.WeierstrassDividedDepth
