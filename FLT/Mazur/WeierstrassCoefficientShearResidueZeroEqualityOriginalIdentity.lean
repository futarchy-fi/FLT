/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroEqualitySmoothComponents
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroEqualitySmoothComponents
public import FLT.Mazur.WeierstrassCoefficientShearResidueExteriorSmoothOrbit
public import FLT.Mazur.WeierstrassCoefficientShearSmoothOrbitLocus
public import FLT.Mazur.PolygonSmoothComponentMembership

/-!
# The original zero's connected smooth component in the ZeroEquality residue model

The original zero lies in the independently retained smooth orbit. The
pinching calculation identifies its entire connected component with that
full orbit, preserving its embedding and original contraction inverse image.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing MonoidalCategory MonObj
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (he : 2 * (0 + (s + 1)) = depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "Z" => coefficientShearResidueZeroEqualityCycleComponent
  hπ hm data s hs he h3 h4 h6next hc
local notation "N" => coefficientShearResidueZeroEqualityCycleCoproduct
  hπ hm data s hs he h3 h4 h6next hc
local notation "J" => coefficientShearResidueZeroEqualityCycleNodes
  hπ hm data s hs he h3 h4 h6next hc
local notation "H" => coefficientShearResidueZeroEqualityCycle_isPushout
  hπ hm data s hs he h3 h4 h6next hc
local notation "B" => coefficientShearSmoothEmbedding hπ data Q r (s + 1) hs
local notation "p" => coefficientShearGluedProjection hπ data Q r (s + 1) hs
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "d" => data ⟨1, by omega⟩
local notation "hres" => nodalDepth_residue_uniformizer hm

/-- The complete punctured exterior is exactly the independently retained original smooth orbit. -/
theorem coefficientShearResidueZeroEquality_exterior_smoothOrbit_range :
    Set.range ((PolygonPinching.torusToComponent Q).left ≫ Z 0) = Set.range B := by
  rw [coefficientShearResidueZeroEqualityCycleComponent_exterior]
  exact coefficientShearResidueExteriorLift_smoothOrbit_range
    hπ data (s + 1) hs d (by dsimp; omega) hres a ha

/-- The actual original zero has the entire retained smooth orbit as its connected component. -/
theorem coefficientShearResidueZeroEquality_originalZero_component_image (x : Spec (.of Q)) :
    let _ : LocallyOfFinitePresentation g :=
      coefficientShearResidueZeroEqualityStructure_lfp
        hπ hm data s hs he h3 h4 h6next hc
    (g).smoothLocus.ι '' connectedComponent
        (coefficientShearOriginalSmoothZero hπ data Q r (s + 1) hs x) = Set.range B := by
  let _ : LocallyOfFinitePresentation g :=
    coefficientShearResidueZeroEqualityStructure_lfp
      hπ hm data s hs he h3 h4 h6next hc
  let _ : LocallyOfFinitePresentation (Over.mk g).hom :=
    coefficientShearResidueZeroEqualityStructure_lfp
      hπ hm data s hs he h3 h4 h6next hc
  have hz : (g).smoothLocus.ι
      (coefficientShearOriginalSmoothZero hπ data Q r (s + 1) hs x) ∈ Set.range B := by
    refine ⟨integralSmoothZero (W.map (algebraMap R Q)) x, ?_⟩
    exact (congrArg (fun f => f x)
      (coefficientShearOriginalSmoothZero_inclusion hπ data Q r (s + 1) hs)).symm
  have hext := coefficientShearResidueZeroEquality_exterior_smoothOrbit_range
    hπ hm data s hs he h3 h4 h6next hc
  have h0 : (ZMod.finEquiv (2 * s + 2)).symm 0 = 0 := by simp
  have hmem : (Over.mk g).hom.smoothLocus.ι
      (coefficientShearOriginalSmoothZero hπ data Q r (s + 1) hs x) ∈
      Set.range (PolygonPinching.torusToComponent Q ≫
        PolygonPinching.componentι Q (2 * s + 2)
          ((ZMod.finEquiv (2 * s + 2)).symm 0) ≫ N).left := by
    simp only [Over.comp_left, coefficientShearResidueZeroEqualityCycleCoproduct_ι, h0]
    exact hext.symm ▸ hz
  have h := PolygonPinching.smooth_connectedComponent_image_of_mem
    Q (2 * s + 2) (by omega) N J H 0
    (coefficientShearOriginalSmoothZero hπ data Q r (s + 1) hs x) hmem
  simp only [Over.comp_left, coefficientShearResidueZeroEqualityCycleCoproduct_ι, h0] at h
  convert h.trans hext using 1
  rfl

/-- The original identity component is the full inverse image of the original smooth cubic open. -/
theorem coefficientShearResidueZeroEquality_originalZero_component_contraction
    (x : Spec (.of Q)) :
    let _ : LocallyOfFinitePresentation g :=
      coefficientShearResidueZeroEqualityStructure_lfp
        hπ hm data s hs he h3 h4 h6next hc
    (g).smoothLocus.ι '' connectedComponent
        (coefficientShearOriginalSmoothZero hπ data Q r (s + 1) hs x) =
      (p ≫ finiteGlobalContraction hπ data (s + 1) hs) ⁻¹'
        (integralSmoothOpen W : Set _) := by
  let _ : LocallyOfFinitePresentation g :=
    coefficientShearResidueZeroEqualityStructure_lfp
      hπ hm data s hs he h3 h4 h6next hc
  exact (coefficientShearResidueZeroEquality_originalZero_component_image
    hπ hm data s hs he h3 h4 h6next hc x).trans
      (coefficientShearSmoothEmbedding_contraction_range hπ data Q r (s + 1) hs)

end FLT.Mazur.WeierstrassDividedDepth
