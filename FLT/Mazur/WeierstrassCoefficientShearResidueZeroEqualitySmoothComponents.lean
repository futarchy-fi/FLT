/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroEqualityPolygonIso
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroEqualityPolygonIso
public import FLT.Mazur.PolygonSmoothConnectedComponents
import all FLT.Mazur.PolygonSmoothConnectedComponents
import all FLT.Mazur.WeierstrassCoefficientShearGluing

/-!
# The complete smooth components of the ZeroEquality residue model

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
local notation "G" => PolygonSplitGroup.model Q (2 * s + 2)

include hm he h3 h4 h6next hc in
/-- The actual residue equation gluing is locally of finite presentation. -/
theorem coefficientShearResidueZeroEqualityStructure_lfp : LocallyOfFinitePresentation g :=
  PolygonPinching.polygon_lfp Q (2 * s + 2) (by omega) N J H

/-- The full actual smooth locus has the original Laurent component coordinates. -/
def coefficientShearResidueZeroEqualitySmoothIso :
    let _ : LocallyOfFinitePresentation (Over.mk g).hom :=
     coefficientShearResidueZeroEqualityStructure_lfp hπ hm data s hs he h3 h4 h6next hc
    PolygonPinching.smoothPolygon Q (C := Over.mk g) ≅ G := by
  let _ : LocallyOfFinitePresentation (Over.mk g).hom :=
    coefficientShearResidueZeroEqualityStructure_lfp hπ hm data s hs he h3 h4 h6next hc
  exact PolygonPinching.smoothIso Q (2 * s + 2) (by omega) N J H

include hm he h3 h4 h6next hc in
/-- Every smooth point is on one of the actual punctured normalization components. -/
theorem coefficientShearResidueZeroEquality_smooth_range :
    let _ : LocallyOfFinitePresentation (Over.mk g).hom :=
     coefficientShearResidueZeroEqualityStructure_lfp hπ hm data s hs he h3 h4 h6next hc
    ((Over.mk g).hom.smoothLocus : Set (Over.mk g).left) =
      ⋃ i : Fin (2 * s + 2), Set.range ((PolygonPinching.torusToComponent Q).left ≫ Z i) := by
  let _ : LocallyOfFinitePresentation (Over.mk g).hom :=
    coefficientShearResidueZeroEqualityStructure_lfp hπ hm data s hs he h3 h4 h6next hc
  have h := PolygonPinching.smooth_range Q (2 * s + 2) (by omega) N J H
  simp only [Over.comp_left, coefficientShearResidueZeroEqualityCycleCoproduct_ι] at h
  convert h using 1

/-- Each complete connected smooth component retains its independent normalization image. -/
theorem coefficientShearResidueZeroEquality_component_image (i : ZMod (2 * s + 2))
    (x : (MultiplicativeGroupScheme.gm Q).left) :
    let _ : LocallyOfFinitePresentation (Over.mk g).hom :=
     coefficientShearResidueZeroEqualityStructure_lfp hπ hm data s hs he h3 h4 h6next hc
    (Over.mk g).hom.smoothLocus.ι '' connectedComponent
        ((PolygonPinching.smoothComponent Q (2 * s + 2) (by omega) N J H i).left x) =
      Set.range ((PolygonPinching.torusToComponent Q).left ≫
        Z ((ZMod.finEquiv (2 * s + 2)).symm i)) := by
  let _ : LocallyOfFinitePresentation (Over.mk g).hom :=
    coefficientShearResidueZeroEqualityStructure_lfp hπ hm data s hs he h3 h4 h6next hc
  have h := PolygonPinching.smoothComponent_connectedComponent_image
    Q (2 * s + 2) (by omega) N J H i x
  simp only [Over.comp_left, coefficientShearResidueZeroEqualityCycleCoproduct_ι] at h
  convert h using 1

/-- The split identity's entire connected smooth component is the punctured exterior. -/
theorem coefficientShearResidueZeroEquality_identity_component_image (x : Spec (.of Q)) :
    let _ : LocallyOfFinitePresentation (Over.mk g).hom :=
     coefficientShearResidueZeroEqualityStructure_lfp hπ hm data s hs he h3 h4 h6next hc
    (Over.mk g).hom.smoothLocus.ι '' connectedComponent
        ((η[G] ≫ (coefficientShearResidueZeroEqualitySmoothIso
          hπ hm data s hs he h3 h4 h6next hc).inv).left x) =
      Set.range ((PolygonPinching.torusToComponent Q).left ≫ Z 0) := by
  let _ : LocallyOfFinitePresentation (Over.mk g).hom :=
    coefficientShearResidueZeroEqualityStructure_lfp hπ hm data s hs he h3 h4 h6next hc
  have h := PolygonPinching.smoothIdentity_connectedComponent_image
    Q (2 * s + 2) (by omega) N J H x
  simp only [Over.comp_left, coefficientShearResidueZeroEqualityCycleCoproduct_ι] at h
  unfold coefficientShearResidueZeroEqualitySmoothIso
  convert h using 1

end FLT.Mazur.WeierstrassDividedDepth
