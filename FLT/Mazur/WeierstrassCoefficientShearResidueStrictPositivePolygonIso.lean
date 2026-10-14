/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositivePinchingColimit
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositivePinchingColimit
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveCycleReflection
public import FLT.Mazur.PolygonCyclicPushout

/-!
# The strict positive-start model is the full original cyclic polygon

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
local notation "C" => coefficientShearResidueStrictPositiveCycleComponent
  hπ hm data s hs hk hstart h3 h4 h6 hc
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "N" => coefficientShearResidueStrictPositiveCycleCoproduct
  hπ hm data s hs hk hstart h3 h4 h6 hc
local notation "J" => coefficientShearResidueStrictPositiveCycleNodes
  hπ hm data s hs hk hstart h3 h4 h6 hc
local notation "P" => PolygonCyclicAtlas.polygon Q (2 * s + 5) (by omega)
local notation "PN" => PolygonCyclicAtlas.normalization Q (2 * s + 5) (by omega)
local notation "PJ" => PolygonCyclicAtlas.nodes Q (2 * s + 5) (by omega)

/-- The explicit full cyclic polygon is the original strict positive-start equation gluing. -/
@[irreducible] def coefficientShearResidueStrictPositivePolygonIso : P ≅ Over.mk g :=
  (PolygonCyclicPushout.isPushout Q (2 * s + 5) (by omega) (by omega)).isoIsPushout _ _
    (coefficientShearResidueStrictPositiveCycle_isPushout hπ hm data s hs hk hstart h3 h4 h6 hc)
local notation "I" => coefficientShearResidueStrictPositivePolygonIso
  hπ hm data s hs hk hstart h3 h4 h6 hc

/-- The polygon comparison retains the entire original normalization coproduct. -/
@[reassoc] theorem coefficientShearResidueStrictPositivePolygonIso_normalization :
    PN ≫ (I).hom = N := by
  rw [coefficientShearResidueStrictPositivePolygonIso, IsPushout.inl_isoIsPushout_hom]

/-- The polygon comparison retains the entire original node coproduct. -/
@[reassoc] theorem coefficientShearResidueStrictPositivePolygonIso_nodes : PJ ≫ (I).hom = J := by
  rw [coefficientShearResidueStrictPositivePolygonIso, IsPushout.inr_isoIsPushout_hom]

/-- Every complete polygon parameter maps to its independently constructed component. -/
@[reassoc] theorem coefficientShearResidueStrictPositivePolygonIso_component (i : Fin (2 * s + 5)) :
    PolygonCyclicAtlas.componentMap Q (2 * s + 5) (by omega) i ≫ (I).hom.left = C i := by
  have H := congrArg (fun f => (PolygonPinching.componentι Q (2 * s + 5) i ≫ f).left)
    (coefficientShearResidueStrictPositivePolygonIso_normalization
      hπ hm data s hs hk hstart h3 h4 h6 hc)
  simpa only [← Category.assoc, PolygonCyclicAtlas.componentι_normalization,
    Over.comp_left, Over.homMk_left, coefficientShearResidueStrictPositiveCycleCoproduct_ι] using H

/-- The original polygon's exterior is the whole ordered residue normalization. -/
@[reassoc] theorem coefficientShearResidueStrictPositivePolygonIso_exterior :
    PolygonCyclicAtlas.componentMap Q (2 * s + 5) (by omega) 0 ≫ (I).hom.left =
      coefficientShearResidueExteriorLift hπ data (s + 1) hs (data ⟨0, Nat.zero_lt_succ n⟩)
        (by dsimp; omega) (nodalDepth_residue_uniformizer hm)
        (residueTangentComponentUnit W h3 h4 hc) := by
  rw [coefficientShearResidueStrictPositivePolygonIso_component,
    coefficientShearResidueStrictPositiveCycleComponent_exterior]

end FLT.Mazur.WeierstrassDividedDepth
