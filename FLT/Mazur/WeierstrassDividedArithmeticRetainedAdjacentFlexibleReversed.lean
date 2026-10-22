/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedAdjacentFlexiblePreMiddleSmoothCover

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
local notation "out" => arithmeticRetainedAdjacentFlexiblePreMiddleLocalOutput
  node data m k hk i hi hiNext hiLast hpre hstage
local notation "swap" => (pullbackSymmetry g f).hom

local instance arithmeticRetainedAdjacentFlexibleReversedStructure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data k hk m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- Include the same actual local source with the original input order reversed. -/
def arithmeticRetainedAdjacentFlexibleReversedInclusion
    (b : RetainedAdjacentFlexiblePreMiddleLocalIndex) : X b ⟶ pullback g f :=
  inc b ≫ (pullbackSymmetry g f).inv

local notation "rev" => arithmeticRetainedAdjacentFlexibleReversedInclusion
  node data m k hk i hi hiNext hiLast hpre hstage

/-- Reversing the input order preserves the open immersion of every local source. -/
instance arithmeticRetainedAdjacentFlexibleReversedInclusion_isOpenImmersion
    (b : RetainedAdjacentFlexiblePreMiddleLocalIndex) : IsOpenImmersion (rev b) := by
  dsimp only [arithmeticRetainedAdjacentFlexibleReversedInclusion]
  infer_instance

/-- The same whole quotient output retains the first reversed coefficient morphism. -/
@[reassoc] theorem arithmeticRetainedAdjacentFlexibleReversedOutput_base
    (b : RetainedAdjacentFlexiblePreMiddleLocalIndex) :
    out b ≫ pullback.fst q t = rev b ≫ pullback.fst g f ≫ g := by
  rw [arithmeticRetainedAdjacentFlexiblePreMiddleLocalOutput_base,
    arithmeticRetainedAdjacentFlexibleReversedInclusion, Category.assoc,
    pullbackSymmetry_inv_comp_fst_assoc, pullback.condition]

/-- Every smooth reversed pair lies in one of the actual local-source images. -/
theorem arithmeticRetainedAdjacentFlexibleReversedLocal_exists
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
  obtain ⟨b, z, hz⟩ := arithmeticRetainedAdjacentFlexiblePreMiddleLocal_exists
    node data m k hk i hi hiNext hiLast hpre hstage hgen (swap p) hfst hsnd
  refine ⟨b, z, ?_⟩
  change (pullbackSymmetry g f).inv (inc b z) = p
  rw [hz]
  exact congrArg (fun morphism => morphism p) (Iso.hom_inv_id (pullbackSymmetry g f))

/-- The full original smooth domain with input order reversed. -/
def arithmeticRetainedAdjacentFlexibleReversedSmoothOpen : (pullback g f).Opens :=
  (pullback.fst g f ≫ chart d) ⁻¹ᵁ (s).smoothLocus ⊓
    (pullback.snd g f ≫ chart c) ⁻¹ᵁ (s).smoothLocus

local notation "A" => arithmeticRetainedAdjacentFlexibleReversedSmoothOpen node data m k hk i

/-- Restrict each genuine source image to the full reversed smooth pair. -/
def arithmeticRetainedAdjacentFlexibleReversedSmoothChart
    (b : RetainedAdjacentFlexiblePreMiddleLocalIndex) : (A).toScheme.Opens :=
  (A).ι ⁻¹ᵁ (rev b).opensRange

local notation "C" => arithmeticRetainedAdjacentFlexibleReversedSmoothChart
  node data m k hk i hi hiNext hiLast hpre hstage

/-- Recover the original source over the complete reversed smooth chart. -/
def arithmeticRetainedAdjacentFlexibleReversedSmoothLift
    (b : RetainedAdjacentFlexiblePreMiddleLocalIndex) : (C b).toScheme ⟶ X b :=
  ((A).ι ∣_ (rev b).opensRange) ≫ (rev b).isoOpensRange.inv

local notation "lift" => arithmeticRetainedAdjacentFlexibleReversedSmoothLift
  node data m k hk i hi hiNext hiLast hpre hstage

/-- The lift retains both reversed inputs as whole scheme morphisms. -/
@[reassoc] theorem arithmeticRetainedAdjacentFlexibleReversedSmoothLift_inclusion
    (b : RetainedAdjacentFlexiblePreMiddleLocalIndex) :
    lift b ≫ rev b = (C b).ι ≫ (A).ι := by
  rw [arithmeticRetainedAdjacentFlexibleReversedSmoothLift, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
  rfl

/-- The reversed smooth chart retains its whole quotient-valued output. -/
def arithmeticRetainedAdjacentFlexibleReversedSmoothOutput
    (b : RetainedAdjacentFlexiblePreMiddleLocalIndex) : (C b).toScheme ⟶ pullback q t :=
  lift b ≫ out b

/-- The output retains the coefficient morphism in reversed input order. -/
@[reassoc] theorem arithmeticRetainedAdjacentFlexibleReversedSmoothOutput_base
    (b : RetainedAdjacentFlexiblePreMiddleLocalIndex) :
    arithmeticRetainedAdjacentFlexibleReversedSmoothOutput
      node data m k hk i hi hiNext hiLast hpre hstage b ≫ pullback.fst q t =
        (C b).ι ≫ (A).ι ≫ pullback.fst g f ≫ g := by
  rw [arithmeticRetainedAdjacentFlexibleReversedSmoothOutput, Category.assoc,
    arithmeticRetainedAdjacentFlexibleReversedOutput_base,
    arithmeticRetainedAdjacentFlexibleReversedSmoothLift_inclusion_assoc]

/-- All smooth reversed pairs are covered, with no original coordinate puncture. -/
theorem arithmeticRetainedAdjacentFlexibleReversedSmoothChart_covers
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (⨆ b, C b) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨b, z, hz⟩ := arithmeticRetainedAdjacentFlexibleReversedLocal_exists
    node data m k hk i hi hiNext hiLast hpre hstage hgen p.val p.property.1 p.property.2
  exact (le_iSup (fun b => C b) b) (show p ∈ C b from ⟨z, hz⟩)

/-- A genuine open cover of the entire reversed smooth pair. -/
def arithmeticRetainedAdjacentFlexibleReversedSmoothCover
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (A).toScheme.OpenCover :=
  (A).toScheme.openCoverOfIsOpenCover C
    (arithmeticRetainedAdjacentFlexibleReversedSmoothChart_covers
      node data m k hk i hi hiNext hiLast hpre hstage hgen)

end FLT.Mazur.WeierstrassDividedDepth
