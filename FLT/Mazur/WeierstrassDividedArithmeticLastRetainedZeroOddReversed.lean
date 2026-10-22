/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedZeroOddSmoothCover

/-!
# Actual local sources for the odd last-retained/terminal pair

Join the three unshifted normalized domains with both terminal incidence
sources. Each embeds openly in the original pair and retains its quotient output.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j + 1 ≤ n)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "a" => retainedOlderFormulaIndex (j + 1) j (Nat.lt_succ_self j)
local notation "chart" => arithmeticTensorAtlasMap hπ data m (j + 1) hj
local notation "s" => finiteGlobalArithmeticStructure hπ data (j + 1) hj m
local notation "old" => finiteArithmeticNewestTensorChart hπ data m j hj
local notation "next" => finiteArithmeticDividedTensorChart hπ data m (j + 1) hj
local notation "E" => finiteDividedTensorAtlasIso hπ data Q (j + 1) hj
local notation "f" => chart a ≫ s
local notation "f₀" => old ≫ s
local notation "f'" => next ≫ s
local notation "g'" => chart 1 ≫ s
local notation "coords" => arithmeticLastRetainedIndexedCoordinates node data m j hj


local notation "base" => finiteGlobalStructure hπ data (j + 1) hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "g" => g'
variable (hodd : depth = 2 * (j + 1) + 1)
local notation "X" => arithmeticLastRetainedZeroOddLocalSource node data m j hj hodd
local notation "inc" => arithmeticLastRetainedZeroOddLocalInclusion node data m j hj hodd
local notation "out" => arithmeticLastRetainedZeroOddLocalOutput node data m j hj hodd
local notation "swap" => (pullbackSymmetry g f).hom

local instance arithmeticLastRetainedZeroOddReversedStructure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data (j + 1) hj m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- Include the same actual local source with the original input order reversed. -/
def arithmeticLastRetainedZeroOddReversedInclusion
    (b : LastRetainedZeroOddLocalIndex) : X b ⟶ pullback g f :=
  inc b ≫ (pullbackSymmetry g f).inv

local notation "rev" => arithmeticLastRetainedZeroOddReversedInclusion
  node data m j hj hodd

/-- Reversing the input order preserves the open immersion of every local source. -/
instance arithmeticLastRetainedZeroOddReversedInclusion_isOpenImmersion
    (b : LastRetainedZeroOddLocalIndex) : IsOpenImmersion (rev b) := by
  dsimp only [arithmeticLastRetainedZeroOddReversedInclusion]
  infer_instance

/-- The same whole quotient output retains the first reversed coefficient morphism. -/
@[reassoc] theorem arithmeticLastRetainedZeroOddReversedOutput_base
    (b : LastRetainedZeroOddLocalIndex) :
    out b ≫ pullback.fst q t = rev b ≫ pullback.fst g f ≫ g := by
  rw [arithmeticLastRetainedZeroOddLocalOutput_base,
    arithmeticLastRetainedZeroOddReversedInclusion, Category.assoc,
    pullbackSymmetry_inv_comp_fst_assoc, pullback.condition]

/-- Every smooth reversed pair lies in one of the actual local-source images. -/
theorem arithmeticLastRetainedZeroOddReversedLocal_exists
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hzero : j = 0) (p : (pullback g f : Scheme))
    (hs : chart 1 (pullback.fst g f p) ∈ (s).smoothLocus)
    (ht : chart a (pullback.snd g f p) ∈ (s).smoothLocus) :
    ∃ b, ∃ z : X b, rev b z = p := by
  have hfst : chart a (pullback.fst f g (swap p)) ∈ (s).smoothLocus := by
    rw [SchemePairSymmetryPoints.fst_apply]
    exact ht
  have hsnd : chart 1 (pullback.snd f g (swap p)) ∈ (s).smoothLocus := by
    rw [SchemePairSymmetryPoints.snd_apply]
    exact hs
  obtain ⟨b, z, hz⟩ := arithmeticLastRetainedZeroOddLocal_exists
    node data m j hj hodd hgen hzero (swap p) hfst hsnd
  refine ⟨b, z, ?_⟩
  change (pullbackSymmetry g f).inv (inc b z) = p
  rw [hz]
  exact congrArg (fun morphism => morphism p) (Iso.hom_inv_id (pullbackSymmetry g f))

/-- The full original smooth domain with input order reversed. -/
def arithmeticLastRetainedZeroOddReversedSmoothOpen : (pullback g f).Opens :=
  (pullback.fst g f ≫ chart 1) ⁻¹ᵁ (s).smoothLocus ⊓
    (pullback.snd g f ≫ chart a) ⁻¹ᵁ (s).smoothLocus

local notation "A" => arithmeticLastRetainedZeroOddReversedSmoothOpen node data m j hj

/-- Restrict each genuine source image to the full reversed smooth pair. -/
def arithmeticLastRetainedZeroOddReversedSmoothChart
    (b : LastRetainedZeroOddLocalIndex) : (A).toScheme.Opens :=
  (A).ι ⁻¹ᵁ (rev b).opensRange

local notation "C" => arithmeticLastRetainedZeroOddReversedSmoothChart
  node data m j hj hodd

/-- Recover the original source over the complete reversed smooth chart. -/
def arithmeticLastRetainedZeroOddReversedSmoothLift
    (b : LastRetainedZeroOddLocalIndex) : (C b).toScheme ⟶ X b :=
  ((A).ι ∣_ (rev b).opensRange) ≫ (rev b).isoOpensRange.inv

local notation "lift" => arithmeticLastRetainedZeroOddReversedSmoothLift
  node data m j hj hodd

/-- The lift retains both reversed inputs as whole scheme morphisms. -/
@[reassoc] theorem arithmeticLastRetainedZeroOddReversedSmoothLift_inclusion
    (b : LastRetainedZeroOddLocalIndex) :
    lift b ≫ rev b = (C b).ι ≫ (A).ι := by
  rw [arithmeticLastRetainedZeroOddReversedSmoothLift, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
  rfl

/-- The reversed smooth chart retains its whole quotient-valued output. -/
def arithmeticLastRetainedZeroOddReversedSmoothOutput
    (b : LastRetainedZeroOddLocalIndex) : (C b).toScheme ⟶ pullback q t :=
  lift b ≫ out b

/-- The output retains the coefficient morphism in reversed input order. -/
@[reassoc] theorem arithmeticLastRetainedZeroOddReversedSmoothOutput_base
    (b : LastRetainedZeroOddLocalIndex) :
    arithmeticLastRetainedZeroOddReversedSmoothOutput
      node data m j hj hodd b ≫ pullback.fst q t =
        (C b).ι ≫ (A).ι ≫ pullback.fst g f ≫ g := by
  rw [arithmeticLastRetainedZeroOddReversedSmoothOutput, Category.assoc,
    arithmeticLastRetainedZeroOddReversedOutput_base,
    arithmeticLastRetainedZeroOddReversedSmoothLift_inclusion_assoc]

/-- All smooth reversed pairs are covered, with no original coordinate puncture. -/
theorem arithmeticLastRetainedZeroOddReversedSmoothChart_covers
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hzero : j = 0) : (⨆ b, C b) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨b, z, hz⟩ := arithmeticLastRetainedZeroOddReversedLocal_exists
    node data m j hj hodd hgen hzero p.val p.property.1 p.property.2
  exact (le_iSup (fun b => C b) b) (show p ∈ C b from ⟨z, hz⟩)

/-- A genuine open cover of the entire reversed smooth pair. -/
def arithmeticLastRetainedZeroOddReversedSmoothCover
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hzero : j = 0) : (A).toScheme.OpenCover :=
  (A).toScheme.openCoverOfIsOpenCover C
    (arithmeticLastRetainedZeroOddReversedSmoothChart_covers
      node data m j hj hodd hgen hzero)

end FLT.Mazur.WeierstrassDividedDepth
