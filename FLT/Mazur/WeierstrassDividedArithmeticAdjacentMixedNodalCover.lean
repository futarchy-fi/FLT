/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentMixedNodalOutput

/-!
# Full smooth incidence coverage for the retained/terminal transfer

The explicit adjacent transfer supplies the target retained puncture. The
three normalized domains therefore cover its entire smooth incidence source,
without a horizontal puncture premise on either original input.
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
local notation "a" => (Fin.succ ⟨j - k, by omega⟩ : Fin (j + 3))
local notation "b" => (Fin.succ ⟨j - (k + 1), by omega⟩ : Fin (j + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj
local notation "fa" => (O b).ι ≫ chart b ≫ s
local notation "fb" => (O 1).ι ≫ chart 1 ≫ s
local notation "f" => chart a ≫ s
local notation "f'" => chart b ≫ s
local notation "g" => chart 1 ≫ s
local notation "B" => arithmeticFixedAdjacentPairOpen hπ data m j hj k hk g
local notation "transfer" => arithmeticFixedAdjacentPairTransfer hπ data m j hj k hk g
local notation "x" => (B).ι ≫ pullback.fst f g
local notation "y" => (B).ι ≫ pullback.snd f g
local notation "z" => transfer ≫ pullback.fst f' g
local notation "w" => transfer ≫ pullback.snd f' g
local notation "D" => arithmeticAdjacentMixedNodalSmoothOpen node data m j hj k hk
local notation "T" => arithmeticAdjacentMixedNodalTarget node data m j hj k hk
local notation "next" => data ⟨k + 2, by omega⟩
local notation "I" => (arithmeticRetainedTensorIso hπ data m j hj (k + 1) (by omega)).inv
local notation "u" => WeierstrassSuccessiveX.tensorCoord W (π ^ (0 + (k + 1))) π
  (next).b3 (next).b4 (next).b6 Q 2

/-- The actual transfer forces the new retained puncture throughout the smooth incidence domain. -/
theorem arithmeticAdjacentMixedNodalTarget_punctured (p : (D).toScheme) :
    u ∉ (I ((O b).ι (pullback.fst fa fb (T p)))).asIdeal := by
  have he := congrArg (fun v => v p)
    (arithmeticAdjacentMixedNodalTarget_coordinate node data m j hj k hk)
  change (O b).ι (pullback.fst fa fb (T p)) =
    pullback.fst f' g (transfer ((D).ι p)) at he
  rw [he]
  exact arithmeticFixedAdjacentPairTransfer_punctured hπ data m j hj k hk g ((D).ι p)

variable (hdepth : 2 * j ≤ depth) (hnear : depth ≤ (k + 1) + 2 * j)
local notation "C" => arithmeticAdjacentMixedNodalChart node data m j hj k hk hdepth hnear

/-- Every smooth boundary point reaches an actual normalized quotient-output domain. -/
theorem arithmeticAdjacentMixedNodalChart_exists (p : (D).toScheme) : ∃ c, p ∈ C c := by
  apply arithmeticMixedNodalReflectedChart_near
    node data m j hj (k + 1) (by omega) hdepth hnear (by omega) (T p)
  intro hz
  apply arithmeticAdjacentMixedNodalTarget_punctured node data m j hj k hk p
  exact (arithmeticMixedFormulaInput_x_iff
    hπ data m j hj (k + 1) j (by omega) le_rfl (T p)).mp hz

/-- The normalized output charts exhaust the entire original smooth incidence domain. -/
theorem arithmeticAdjacentMixedNodalChart_covers : (⨆ c, C c) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨c, hc⟩ := arithmeticAdjacentMixedNodalChart_exists
    node data m j hj k hk hdepth hnear p
  exact (le_iSup (fun c => C c) c) hc

/-- An actual cover of the complete smooth retained-transfer source with whole outputs. -/
def arithmeticAdjacentMixedNodalCover : (D).toScheme.OpenCover :=
  (D).toScheme.openCoverOfIsOpenCover C
    (arithmeticAdjacentMixedNodalChart_covers node data m j hj k hk hdepth hnear)

end FLT.Mazur.WeierstrassDividedDepth
