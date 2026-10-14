/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitCartesian
public import FLT.Mazur.PolygonSmoothConnectedComponents
public import FLT.Mazur.PolygonSplitGroupConnected
import all FLT.Mazur.WeierstrassDividedPositiveSplitSmoothGroup

/-!
# Complete smooth components and the original contraction inverse image

Every connected component retains its punctured original projective component.
The component of the actual zero is precisely the full preimage of the original smooth cubic.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing MonoidalCategory MonObj
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "f" => finiteGlobalStructure hπ data (s + 1) hs
local notation "p" => pullback.fst q f
local notation "G" => PolygonSplitGroup.model K (2 * s + 5)
local notation "e" => positiveSplitCycleSmoothIso hπ data D s hs hstart hk hp

local notation "Z" => positiveSplitCycleComponent hπ data D s hs hstart hk hp
local notation "N" => positiveSplitCycleNormalization hπ data D s hs hstart hk hp
local notation "Q" => positiveSplitCycleNodes hπ data D s hs hstart hk hp
local notation "H" => positiveSplitCycleCocone_isPushout hπ data D s hs hstart hk hp

/-- Each full connected smooth component retains its original punctured projective image. -/
theorem positiveSplitCycleSmooth_component_image (i : ZMod (2 * s + 5))
    (x : (MultiplicativeGroupScheme.gm K).left) :
    let _ : LocallyOfFinitePresentation (Over.mk p).hom :=
      positiveSplitCycleStructure_lfp hπ data D s hs hstart hk hp
    (Over.mk p).hom.smoothLocus.ι '' connectedComponent
        ((PolygonPinching.smoothComponent K (2 * s + 5) (by omega) N Q H i).left x) =
      Set.range (PolygonPinching.torusToComponent K ≫
        Z ((ZMod.finEquiv (2 * s + 5)).symm i)).left := by
  let _ : LocallyOfFinitePresentation (Over.mk p).hom :=
      positiveSplitCycleStructure_lfp hπ data D s hs hstart hk hp
  simpa only [positiveSplitCycleNormalization_ι] using
    PolygonPinching.smoothComponent_connectedComponent_image K (2 * s + 5) (by omega) N Q H i x

/-- The entire original smooth residue embedding is the full contraction inverse image. -/
theorem positiveSplitOriginalSmoothMap_range_contraction :
    Set.range (positiveSplitOriginalSmoothMap hπ data D s hs hk) =
      (pullback.snd q f ≫ finiteGlobalContraction hπ data (s + 1) hs) ⁻¹'
        (WeierstrassIntegralChart.integralSmoothOpen W : Set _) := by
  rw [positiveSplitOriginalSmoothMap_range_specialization, finiteGlobalSmoothEmbedding_range]
  rfl

/-- No point over the original smooth cubic is omitted from the actual smooth zero component. -/
theorem positiveSplitSmoothZero_component_contraction (x : Spec (.of K)) :
    let _ := positiveSplitCycleStructure_lfp hπ data D s hs hstart hk hp
    (p).smoothLocus.ι ''
        connectedComponent (positiveSplitSmoothZero hπ data D s hs hstart hk hp x) =
      (pullback.snd q f ≫ finiteGlobalContraction hπ data (s + 1) hs) ⁻¹'
        (WeierstrassIntegralChart.integralSmoothOpen W : Set _) := by
  let _ := positiveSplitCycleStructure_lfp hπ data D s hs hstart hk hp
  exact (positiveSplitOriginalSmoothMap_component hπ data D s hs hstart hk hp x).trans
    (positiveSplitOriginalSmoothMap_range_contraction hπ data D s hs hk)

end FLT.Mazur.WeierstrassDividedDepth
