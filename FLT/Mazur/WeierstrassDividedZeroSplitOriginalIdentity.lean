/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclePolygonIso
public import FLT.Mazur.WeierstrassDividedZeroExteriorSmoothOrbit
public import FLT.Mazur.WeierstrassDividedCoefficientSmoothLocus
public import FLT.Mazur.PolygonSmoothComponentMembership
import all FLT.Mazur.WeierstrassDividedZeroCyclePushout

/-!
# The original zero component of the split start-zero split model

The whole punctured exterior is the independently retained original smooth
orbit. Its original zero determines the complete component in the actual fiber.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "f" => finiteGlobalStructure hπ data (s + 1) hs
local notation "p" => (pullback.fst q f :
  finiteGlobalTensorModel hπ data K (s + 1) hs ⟶ Spec (.of K))
local notation "Z" => zeroSplitCycleComponent hπ data D s hs hstart hk hp
local notation "N" => zeroSplitCycleNormalization hπ data D s hs hstart hk hp
local notation "Q" => zeroSplitCycleNodes hπ data D s hs hk hp
local notation "H" => zeroSplitCycleCocone_isPushout hπ data D s hs hstart hp
local notation "B" => finiteGlobalSmoothCoefficientEmbedding K hπ data (s + 1) hs

include D hstart hk hp in
/-- The actual original split residue model is locally of finite presentation. -/
theorem zeroSplitOriginalStructure_lfp : LocallyOfFinitePresentation p :=
  PolygonPinching.polygon_lfp K (2 * s + 3) (by omega) N Q H

/-- The full punctured exterior is precisely the independent original smooth embedding. -/
theorem zeroSplitOriginal_exterior_range :
    Set.range ((PolygonPinching.torusToComponent K).left ≫ (Z 0).left) = Set.range B := by
  rw [zeroSplitCycleComponent_exterior]
  exact finalZeroExteriorComponent_smoothOrbit_range hπ data D s hs hstart hk

/-- The original zero has the entire independently retained smooth orbit as its component. -/
theorem zeroSplitOriginalZero_component_image (x : Spec (.of K)) :
    let _ : LocallyOfFinitePresentation p :=
      zeroSplitOriginalStructure_lfp hπ data D s hs hstart hk hp
    (p).smoothLocus.ι '' connectedComponent
      (finiteGlobalOriginalCoefficientSmoothZero hπ data K (s + 1) hs x) = Set.range B := by
  let _ : LocallyOfFinitePresentation p :=
    zeroSplitOriginalStructure_lfp hπ data D s hs hstart hk hp
  let _ : LocallyOfFinitePresentation (Over.mk p).hom :=
    zeroSplitOriginalStructure_lfp hπ data D s hs hstart hk hp
  have hz : (p).smoothLocus.ι
      (finiteGlobalOriginalCoefficientSmoothZero hπ data K (s + 1) hs x) ∈ Set.range B := by
    refine ⟨integralSmoothZero (W.map (algebraMap R K)) x, ?_⟩
    exact (congrArg (fun a => a x)
      (finiteGlobalOriginalCoefficientSmoothZero_inclusion hπ data K (s + 1) hs)).symm
  have hext := zeroSplitOriginal_exterior_range hπ data D s hs hstart hk hp
  have h0 : (ZMod.finEquiv (2 * s + 3)).symm 0 = 0 := by simp
  have hmem : (Over.mk p).hom.smoothLocus.ι
      (finiteGlobalOriginalCoefficientSmoothZero hπ data K (s + 1) hs x) ∈
      Set.range (PolygonPinching.torusToComponent K ≫
        PolygonPinching.componentι K (2 * s + 3)
          ((ZMod.finEquiv (2 * s + 3)).symm 0) ≫ N).left := by
    simp only [zeroSplitCycleNormalization_ι, h0, Over.comp_left]
    exact hext.symm ▸ hz
  have h := PolygonPinching.smooth_connectedComponent_image_of_mem K (2 * s + 3)
    (by omega) N Q H 0 (finiteGlobalOriginalCoefficientSmoothZero hπ data K (s + 1) hs x) hmem
  simp only [zeroSplitCycleNormalization_ι, h0, Over.comp_left] at h
  convert h.trans hext using 1
  rfl

/-- The original identity component is the exact inverse image of the integral smooth cubic. -/
theorem zeroSplitOriginalZero_component_contraction (x : Spec (.of K)) :
    let _ : LocallyOfFinitePresentation p :=
      zeroSplitOriginalStructure_lfp hπ data D s hs hstart hk hp
    (p).smoothLocus.ι '' connectedComponent
      (finiteGlobalOriginalCoefficientSmoothZero hπ data K (s + 1) hs x) =
        (pullback.snd q f ≫ finiteGlobalContraction hπ data (s + 1) hs) ⁻¹'
          (integralSmoothOpen W : Set _) := by
  let _ : LocallyOfFinitePresentation p :=
    zeroSplitOriginalStructure_lfp hπ data D s hs hstart hk hp
  dsimp only
  rw [zeroSplitOriginalZero_component_image hπ data D s hs hstart hk hp x,
    finiteGlobalSmoothCoefficientEmbedding_range, finiteGlobalSmoothEmbedding_range]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
