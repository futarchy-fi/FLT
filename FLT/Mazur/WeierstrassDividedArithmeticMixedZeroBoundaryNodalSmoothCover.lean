/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticMixedZeroBoundaryNodalLocalCover

/-!
# A full smooth cover for creation-zero retained/terminal pairs

Restrict the four genuine source images to the unchanged original smooth
pair. Every chart recovers its source and carries its whole quotient output;
no puncture is imposed on the original inputs.
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
local notation "b" => (Fin.succ ⟨j - (k + 1), by omega⟩ : Fin (j + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "fb" => (O 1).ι ≫ chart 1 ≫ s
local notation "f" => chart a ≫ s
local notation "f'" => chart b ≫ s
local notation "g" => chart 1 ≫ s
local notation "B" => arithmeticFixedAdjacentPairOpen hπ data m j hj k hk g
local notation "transfer" => arithmeticFixedAdjacentPairTransfer hπ data m j hj k hk g
local notation "D" => arithmeticAdjacentMixedNodalSmoothOpen node data m j hj k hk
variable (hdepth : 2 * j ≤ depth) (hnear : depth ≤ (k + 1) + 2 * j)
local notation "E" => arithmeticRetainedTerminalOpen
  hπ data m j hj k j (by omega) le_rfl (by omega)
local notation "C" => arithmeticAdjacentMixedNodalChart
  node data m j hj k hk hdepth (by omega)
local notation "inc" => arithmeticSmoothPairInclusion hπ data m j hj a 1

local notation "X" => arithmeticMixedZeroBoundaryNodalLocalSource node data m j hj k hk hdepth hnear
local notation "J" => arithmeticMixedZeroBoundaryNodalLocalInclusion
  node data m j hj k hk hdepth hnear

local instance arithmeticMixedZeroBoundaryNodalSmoothCover_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data j hj m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- The full original smooth retained/terminal pair, without either puncture. -/
def arithmeticMixedZeroBoundaryNodalSmoothOpen : (pullback f g).Opens :=
  (pullback.fst f g ≫ chart a) ⁻¹ᵁ (s).smoothLocus ⊓
    (pullback.snd f g ≫ chart 1) ⁻¹ᵁ (s).smoothLocus

local notation "A" => arithmeticMixedZeroBoundaryNodalSmoothOpen node data m j hj k

/-- Restrict each genuine source image to the full smooth original pair. -/
def arithmeticMixedZeroBoundaryNodalSmoothChart (c : MixedZeroBoundaryNodalLocalIndex) :
    (A).toScheme.Opens := (A).ι ⁻¹ᵁ (J c).opensRange

local notation "V" => arithmeticMixedZeroBoundaryNodalSmoothChart node data m j hj k hk hdepth hnear

/-- Recover the genuine local source from its open image. -/
def arithmeticMixedZeroBoundaryNodalSmoothLift (c : MixedZeroBoundaryNodalLocalIndex) :
    (V c).toScheme ⟶ X c := ((A).ι ∣_ (J c).opensRange) ≫ (J c).isoOpensRange.inv

local notation "L" => arithmeticMixedZeroBoundaryNodalSmoothLift node data m j hj k hk hdepth hnear

/-- The lift preserves the whole original pair morphism, including both inputs. -/
@[reassoc] theorem arithmeticMixedZeroBoundaryNodalSmoothLift_inclusion
    (c : MixedZeroBoundaryNodalLocalIndex) : L c ≫ J c = (V c).ι ≫ (A).ι := by
  rw [arithmeticMixedZeroBoundaryNodalSmoothLift, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
  rfl

/-- Every actual smooth chart carries its constructed normalized quotient output. -/
def arithmeticMixedZeroBoundaryNodalSmoothOutput (c : MixedZeroBoundaryNodalLocalIndex) :
    (V c).toScheme ⟶ pullback q t :=
  L c ≫ arithmeticMixedZeroBoundaryNodalLocalOutput node data m j hj k hk hdepth hnear c

/-- The output has the unchanged complete original arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticMixedZeroBoundaryNodalSmoothOutput_base
    (c : MixedZeroBoundaryNodalLocalIndex) :
    arithmeticMixedZeroBoundaryNodalSmoothOutput node data m j hj k hk hdepth hnear c ≫
      pullback.fst q t = (V c).ι ≫ (A).ι ≫ pullback.fst f g ≫ f := by
  rw [arithmeticMixedZeroBoundaryNodalSmoothOutput, Category.assoc,
    arithmeticMixedZeroBoundaryNodalLocalOutput_base,
    arithmeticMixedZeroBoundaryNodalSmoothLift_inclusion_assoc]

/-- No puncture is required on either original smooth input. -/
theorem arithmeticMixedZeroBoundaryNodalSmoothChart_covers
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hk0 : k = 0) : (⨆ c, V c) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨c, z, hz⟩ := arithmeticMixedZeroBoundaryNodalLocal_exists
    node data m j hj k hk hdepth hnear hgen hk0 p.val p.property.1 p.property.2
  exact (le_iSup (fun c => V c) c) ⟨z, hz⟩

/-- A genuine open cover of the entire original smooth retained/terminal pair. -/
def arithmeticMixedZeroBoundaryNodalSmoothCover
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hk0 : k = 0) : (A).toScheme.OpenCover :=
  (A).toScheme.openCoverOfIsOpenCover V
    (arithmeticMixedZeroBoundaryNodalSmoothChart_covers
      node data m j hj k hk hdepth hnear hgen hk0)

end FLT.Mazur.WeierstrassDividedDepth
