/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositivePolygonIso
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositivePolygonIso
public import FLT.Mazur.PolygonSmoothConnectedComponents
import all FLT.Mazur.PolygonSmoothConnectedComponents
import all FLT.Mazur.WeierstrassCoefficientShearGluing

/-!
# The complete smooth components of the StrictPositive residue model

The original pinching maps identify every connected smooth component and
its full image. The split identity has the entire punctured exterior image.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing MonoidalCategory MonObj
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + (s + 1)) < depth)
  (hstart : 0 < start)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "Z" => coefficientShearResidueStrictPositiveCycleComponent
  hπ hm data s hs hk hstart h3 h4 h6 hc
local notation "N" => coefficientShearResidueStrictPositiveCycleCoproduct
  hπ hm data s hs hk hstart h3 h4 h6 hc
local notation "J" => coefficientShearResidueStrictPositiveCycleNodes
  hπ hm data s hs hk hstart h3 h4 h6 hc
local notation "H" => coefficientShearResidueStrictPositiveCycle_isPushout
  hπ hm data s hs hk hstart h3 h4 h6 hc
local notation "G" => PolygonSplitGroup.model Q (2 * s + 5)

include hm hk hstart h3 h4 h6 hc in
/-- The actual residue equation gluing is locally of finite presentation. -/
theorem coefficientShearResidueStrictPositiveStructure_lfp : LocallyOfFinitePresentation g :=
  PolygonPinching.polygon_lfp Q (2 * s + 5) (by omega) N J H

/-- The full actual smooth locus has the original Laurent component coordinates. -/
def coefficientShearResidueStrictPositiveSmoothIso :
    let _ : LocallyOfFinitePresentation (Over.mk g).hom :=
     coefficientShearResidueStrictPositiveStructure_lfp hπ hm data s hs hk hstart h3 h4 h6 hc
    PolygonPinching.smoothPolygon Q (C := Over.mk g) ≅ G := by
  let _ : LocallyOfFinitePresentation (Over.mk g).hom :=
    coefficientShearResidueStrictPositiveStructure_lfp hπ hm data s hs hk hstart h3 h4 h6 hc
  exact PolygonPinching.smoothIso Q (2 * s + 5) (by omega) N J H

include hm hk hstart h3 h4 h6 hc in
/-- Every smooth point is on one of the actual punctured normalization components. -/
theorem coefficientShearResidueStrictPositive_smooth_range :
    let _ : LocallyOfFinitePresentation (Over.mk g).hom :=
     coefficientShearResidueStrictPositiveStructure_lfp hπ hm data s hs hk hstart h3 h4 h6 hc
    ((Over.mk g).hom.smoothLocus : Set (Over.mk g).left) =
      ⋃ i : Fin (2 * s + 5), Set.range ((PolygonPinching.torusToComponent Q).left ≫ Z i) := by
  let _ : LocallyOfFinitePresentation (Over.mk g).hom :=
    coefficientShearResidueStrictPositiveStructure_lfp hπ hm data s hs hk hstart h3 h4 h6 hc
  have h := PolygonPinching.smooth_range Q (2 * s + 5) (by omega) N J H
  simp only [Over.comp_left, coefficientShearResidueStrictPositiveCycleCoproduct_ι] at h
  convert h using 1

/-- Each complete connected smooth component retains its independent normalization image. -/
theorem coefficientShearResidueStrictPositive_component_image (i : ZMod (2 * s + 5))
    (x : (MultiplicativeGroupScheme.gm Q).left) :
    let _ : LocallyOfFinitePresentation (Over.mk g).hom :=
     coefficientShearResidueStrictPositiveStructure_lfp hπ hm data s hs hk hstart h3 h4 h6 hc
    (Over.mk g).hom.smoothLocus.ι '' connectedComponent
        ((PolygonPinching.smoothComponent Q (2 * s + 5) (by omega) N J H i).left x) =
      Set.range ((PolygonPinching.torusToComponent Q).left ≫
        Z ((ZMod.finEquiv (2 * s + 5)).symm i)) := by
  let _ : LocallyOfFinitePresentation (Over.mk g).hom :=
    coefficientShearResidueStrictPositiveStructure_lfp hπ hm data s hs hk hstart h3 h4 h6 hc
  have h := PolygonPinching.smoothComponent_connectedComponent_image
    Q (2 * s + 5) (by omega) N J H i x
  simp only [Over.comp_left, coefficientShearResidueStrictPositiveCycleCoproduct_ι] at h
  convert h using 1

/-- The split identity's entire connected smooth component is the punctured exterior. -/
theorem coefficientShearResidueStrictPositive_identity_component_image (x : Spec (.of Q)) :
    let _ : LocallyOfFinitePresentation (Over.mk g).hom :=
     coefficientShearResidueStrictPositiveStructure_lfp hπ hm data s hs hk hstart h3 h4 h6 hc
    (Over.mk g).hom.smoothLocus.ι '' connectedComponent
        ((η[G] ≫ (coefficientShearResidueStrictPositiveSmoothIso
          hπ hm data s hs hk hstart h3 h4 h6 hc).inv).left x) =
      Set.range ((PolygonPinching.torusToComponent Q).left ≫ Z 0) := by
  let _ : LocallyOfFinitePresentation (Over.mk g).hom :=
    coefficientShearResidueStrictPositiveStructure_lfp hπ hm data s hs hk hstart h3 h4 h6 hc
  have h := PolygonPinching.smoothIdentity_connectedComponent_image
    Q (2 * s + 5) (by omega) N J H x
  simp only [Over.comp_left, coefficientShearResidueStrictPositiveCycleCoproduct_ι] at h
  unfold coefficientShearResidueStrictPositiveSmoothIso
  convert h using 1

end FLT.Mazur.WeierstrassDividedDepth
