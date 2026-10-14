/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroPinchingColimit
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroPinchingColimit
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroEqualityReflection
public import FLT.Mazur.PolygonCyclicPushout

/-!
# The zero-start equality model is the full original cyclic polygon

The pinching universal property identifies the actual coefficient equations
with the explicit polygon, preserving every normalization and node summand.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
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
local notation "C" => coefficientShearResidueZeroEqualityCycleComponent
  hπ hm data s hs he h3 h4 h6next hc
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "N" => coefficientShearResidueZeroEqualityCycleCoproduct
  hπ hm data s hs he h3 h4 h6next hc
local notation "J" => coefficientShearResidueZeroEqualityCycleNodes
  hπ hm data s hs he h3 h4 h6next hc
local notation "P" => PolygonCyclicAtlas.polygon Q (2 * s + 2) (by omega)
local notation "PN" => PolygonCyclicAtlas.normalization Q (2 * s + 2) (by omega)
local notation "PJ" => PolygonCyclicAtlas.nodes Q (2 * s + 2) (by omega)

/-- The explicit full cyclic polygon is the original zero-start equality equation gluing. -/
@[irreducible] def coefficientShearResidueZeroEqualityPolygonIso : P ≅ Over.mk g :=
  (PolygonCyclicPushout.isPushout Q (2 * s + 2) (by omega) (by omega)).isoIsPushout _ _
    (coefficientShearResidueZeroEqualityCycle_isPushout hπ hm data s hs he h3 h4 h6next hc)
local notation "I" => coefficientShearResidueZeroEqualityPolygonIso
  hπ hm data s hs he h3 h4 h6next hc

/-- The polygon comparison retains the entire original normalization coproduct. -/
@[reassoc] theorem coefficientShearResidueZeroEqualityPolygonIso_normalization :
    PN ≫ (I).hom = N := by
  rw [coefficientShearResidueZeroEqualityPolygonIso, IsPushout.inl_isoIsPushout_hom]

/-- The polygon comparison retains the entire original node coproduct. -/
@[reassoc] theorem coefficientShearResidueZeroEqualityPolygonIso_nodes : PJ ≫ (I).hom = J := by
  rw [coefficientShearResidueZeroEqualityPolygonIso, IsPushout.inr_isoIsPushout_hom]

/-- Every complete polygon parameter maps to its independently constructed component. -/
@[reassoc] theorem coefficientShearResidueZeroEqualityPolygonIso_component (i : Fin (2 * s + 2)) :
    PolygonCyclicAtlas.componentMap Q (2 * s + 2) (by omega) i ≫ (I).hom.left = C i := by
  have H := congrArg (fun f => (PolygonPinching.componentι Q (2 * s + 2) i ≫ f).left)
    (coefficientShearResidueZeroEqualityPolygonIso_normalization
      hπ hm data s hs he h3 h4 h6next hc)
  simpa only [← Category.assoc, PolygonCyclicAtlas.componentι_normalization,
    Over.comp_left, Over.homMk_left, coefficientShearResidueZeroEqualityCycleCoproduct_ι] using H

/-- The original polygon's exterior is the whole ordered residue normalization. -/
@[reassoc] theorem coefficientShearResidueZeroEqualityPolygonIso_exterior :
    PolygonCyclicAtlas.componentMap Q (2 * s + 2) (by omega) 0 ≫ (I).hom.left =
      coefficientShearResidueExteriorLift hπ data (s + 1) hs (data ⟨1, by omega⟩)
        (by dsimp; omega) (nodalDepth_residue_uniformizer hm)
        (residueTangentComponentUnit W h3 h4 hc) := by
  rw [coefficientShearResidueZeroEqualityPolygonIso_component,
    coefficientShearResidueZeroEqualityCycleComponent_exterior]

end FLT.Mazur.WeierstrassDividedDepth
