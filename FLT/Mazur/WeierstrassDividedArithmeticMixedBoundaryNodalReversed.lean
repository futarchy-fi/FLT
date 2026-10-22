/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticMixedBoundaryNodalSmoothCover

/-!
# Full normalized covers in the reverse mixed order

Swap each genuine local inclusion and recover its source from the open image.
The entire reversed smooth pair is covered; no equality between swapped
addition formulas is asserted.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  arithmeticRetainedTensorIso olderSuccessiveTensorAtlasIso finiteTensorAtlasObject
  arithmeticFixedAdjacentPairOpen arithmeticFixedAdjacentPairTransfer
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n) (k : ℕ) (hk : k + 2 ≤ j)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "a" => (Fin.succ ⟨j - k,
  Nat.lt_succ_of_le ((Nat.sub_le j k).trans (Nat.le_succ j))⟩ : Fin (j + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "fb" => (O 1).ι ≫ chart 1 ≫ s
local notation "f" => chart a ≫ s
local notation "g" => chart 1 ≫ s
variable (hdepth : 2 * j ≤ depth) (hnear : depth ≤ k + 2 * j)
local notation "X" => arithmeticMixedBoundaryNodalLocalSource
  node data m j hj k hk hdepth hnear
local notation "inc" => arithmeticMixedBoundaryNodalLocalInclusion
  node data m j hj k hk hdepth hnear
local notation "out" => arithmeticMixedBoundaryNodalLocalOutput
  node data m j hj k hk hdepth hnear
local notation "swap" => (pullbackSymmetry g f).hom

local instance arithmeticMixedBoundaryNodalReversedStructure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data j hj m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- Include the same actual local source with the original input order reversed. -/
def arithmeticMixedBoundaryNodalReversedInclusion
    (b : MixedBoundaryNodalLocalIndex) : X b ⟶ pullback g f :=
  inc b ≫ (pullbackSymmetry g f).inv

local notation "rev" => arithmeticMixedBoundaryNodalReversedInclusion
  node data m j hj k hk hdepth hnear

/-- Reversing the input order preserves the open immersion of every local source. -/
instance arithmeticMixedBoundaryNodalReversedInclusion_isOpenImmersion
    (b : MixedBoundaryNodalLocalIndex) : IsOpenImmersion (rev b) := by
  dsimp only [arithmeticMixedBoundaryNodalReversedInclusion]
  infer_instance

/-- The same whole quotient output retains the first reversed coefficient morphism. -/
@[reassoc] theorem arithmeticMixedBoundaryNodalReversedOutput_base
    (b : MixedBoundaryNodalLocalIndex) :
    out b ≫ pullback.fst q t = rev b ≫ pullback.fst g f ≫ g := by
  rw [arithmeticMixedBoundaryNodalLocalOutput_base,
    arithmeticMixedBoundaryNodalReversedInclusion, Category.assoc,
    pullbackSymmetry_inv_comp_fst_assoc, pullback.condition]

/-- Every smooth reversed pair lies in one of the actual local-source images. -/
theorem arithmeticMixedBoundaryNodalReversedLocal_exists
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hk0 : 0 < k) (p : (pullback g f : Scheme))
    (hs : chart 1 (pullback.fst g f p) ∈ (s).smoothLocus)
    (ht : chart a (pullback.snd g f p) ∈ (s).smoothLocus) :
    ∃ b, ∃ z : X b, rev b z = p := by
  have hfst : chart a (pullback.fst f g (swap p)) ∈ (s).smoothLocus := by
    rw [SchemePairSymmetryPoints.fst_apply]
    exact ht
  have hsnd : chart 1 (pullback.snd f g (swap p)) ∈ (s).smoothLocus := by
    rw [SchemePairSymmetryPoints.snd_apply]
    exact hs
  obtain ⟨b, z, hz⟩ := arithmeticMixedBoundaryNodalLocal_exists
    node data m j hj k hk hdepth hnear hgen hk0 (swap p) hfst hsnd
  refine ⟨b, z, ?_⟩
  change (pullbackSymmetry g f).inv (inc b z) = p
  rw [hz]
  exact congrArg (fun morphism => morphism p) (Iso.hom_inv_id (pullbackSymmetry g f))

/-- The full original smooth domain with input order reversed. -/
def arithmeticMixedBoundaryNodalReversedSmoothOpen : (pullback g f).Opens :=
  (pullback.fst g f ≫ chart 1) ⁻¹ᵁ (s).smoothLocus ⊓
    (pullback.snd g f ≫ chart a) ⁻¹ᵁ (s).smoothLocus

local notation "A" => arithmeticMixedBoundaryNodalReversedSmoothOpen node data m j hj k

/-- Restrict each genuine source image to the full reversed smooth pair. -/
def arithmeticMixedBoundaryNodalReversedSmoothChart
    (b : MixedBoundaryNodalLocalIndex) : (A).toScheme.Opens :=
  (A).ι ⁻¹ᵁ (rev b).opensRange

local notation "C" => arithmeticMixedBoundaryNodalReversedSmoothChart
  node data m j hj k hk hdepth hnear

/-- Recover the original source over the complete reversed smooth chart. -/
def arithmeticMixedBoundaryNodalReversedSmoothLift
    (b : MixedBoundaryNodalLocalIndex) : (C b).toScheme ⟶ X b :=
  ((A).ι ∣_ (rev b).opensRange) ≫ (rev b).isoOpensRange.inv

local notation "lift" => arithmeticMixedBoundaryNodalReversedSmoothLift
  node data m j hj k hk hdepth hnear

/-- The lift retains both reversed inputs as whole scheme morphisms. -/
@[reassoc] theorem arithmeticMixedBoundaryNodalReversedSmoothLift_inclusion
    (b : MixedBoundaryNodalLocalIndex) :
    lift b ≫ rev b = (C b).ι ≫ (A).ι := by
  rw [arithmeticMixedBoundaryNodalReversedSmoothLift, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
  rfl

/-- The reversed smooth chart retains its whole quotient-valued output. -/
def arithmeticMixedBoundaryNodalReversedSmoothOutput
    (b : MixedBoundaryNodalLocalIndex) : (C b).toScheme ⟶ pullback q t :=
  lift b ≫ out b

/-- The output retains the coefficient morphism in reversed input order. -/
@[reassoc] theorem arithmeticMixedBoundaryNodalReversedSmoothOutput_base
    (b : MixedBoundaryNodalLocalIndex) :
    arithmeticMixedBoundaryNodalReversedSmoothOutput
      node data m j hj k hk hdepth hnear b ≫ pullback.fst q t =
        (C b).ι ≫ (A).ι ≫ pullback.fst g f ≫ g := by
  rw [arithmeticMixedBoundaryNodalReversedSmoothOutput, Category.assoc,
    arithmeticMixedBoundaryNodalReversedOutput_base,
    arithmeticMixedBoundaryNodalReversedSmoothLift_inclusion_assoc]

/-- All smooth reversed pairs are covered, with no original coordinate puncture. -/
theorem arithmeticMixedBoundaryNodalReversedSmoothChart_covers
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hk0 : 0 < k) : (⨆ b, C b) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨b, z, hz⟩ := arithmeticMixedBoundaryNodalReversedLocal_exists
    node data m j hj k hk hdepth hnear hgen hk0 p.val p.property.1 p.property.2
  exact (le_iSup (fun b => C b) b) (show p ∈ C b from ⟨z, hz⟩)

/-- A genuine open cover of the entire reversed smooth pair. -/
def arithmeticMixedBoundaryNodalReversedSmoothCover
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hk0 : 0 < k) : (A).toScheme.OpenCover :=
  (A).toScheme.openCoverOfIsOpenCover C
    (arithmeticMixedBoundaryNodalReversedSmoothChart_covers
      node data m j hj k hk hdepth hnear hgen hk0)

end FLT.Mazur.WeierstrassDividedDepth
