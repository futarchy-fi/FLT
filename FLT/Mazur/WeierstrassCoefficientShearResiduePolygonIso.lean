/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResiduePinchingColimit
public import FLT.Mazur.PolygonCoconeComparison
import all FLT.Mazur.WeierstrassCoefficientShearResiduePinchingColimit

/-!
# The original nonsplit residue equation gluing is the specified polygon

The comparison follows from the actual pinching universal property and retains
all full original projective components and node sections.
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
  (s : ℕ) (hs : s + 1 ≤ n) (he : 2 * (start + (s + 1)) = depth)
  (hstart : 0 < start)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth)
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "hk" => Nat.le_of_eq he
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "hres" => nodalDepth_residue_uniformizer hm
local notation "F" => coefficientShearResidueExteriorLift hπ data (s + 1) hs d
  (by dsimp; omega) hres a
local notation "B" => coefficientShearResidueBranchComponent
  hπ hm data s hs hk hstart h3 h4 h6 hc
local notation "T" => coefficientShearResidueEqualityComponent
  hπ hm data s hs he h3 h4 h6next hc
local notation "ρ" => ProjectiveLine.endpointReversal Q

local notation "N" => coefficientShearResidueCycleCoproduct
  hπ hm data s hs he hstart h3 h4 h6 h6next hc
local notation "J" => coefficientShearResidueCycleNodes
  hπ hm data s hs he hstart h3 h4 h6 h6next hc
local notation "H" => coefficientShearResidueCycle_isPushout
  hπ hm data s hs he hstart h3 h4 h6 h6next hc
local notation "C" => coefficientShearResidueCycleComponent
  hπ hm data s hs he hstart h3 h4 h6 h6next hc

/-- The same actual pinching diagram is a pushout of underlying schemes. -/
theorem coefficientShearResidueCycle_scheme_isPushout :
    IsPushout (PolygonPinching.toComponents Q (2 * s + 4) (by omega)).left
      (PolygonPinching.toNodes Q (2 * s + 4)).left (N).left (J).left :=
  (H).map (Over.forget _)

/-- The specified polygon is the complete original coefficient equation gluing. -/
def coefficientShearResiduePolygonIso :
    PolygonAtlas.polygon Q (2 * s + 4) ≅ Over.mk g :=
  PolygonPinching.polygonIso Q (2 * s + 4) (by omega) N J H
local notation "I" => coefficientShearResiduePolygonIso
  hπ hm data s hs he hstart h3 h4 h6 h6next hc

/-- The comparison retains the original whole normalization coproduct. -/
@[reassoc] theorem coefficientShearResiduePolygonIso_normalization :
    PolygonAtlas.normalization Q (2 * s + 4) ≫ (I).hom = N :=
  PolygonPinching.normalization_polygonIso Q (2 * s + 4) (by omega) N J H

/-- The comparison retains every original node summand. -/
@[reassoc] theorem coefficientShearResiduePolygonIso_nodes :
    PolygonAtlas.nodes Q (2 * s + 4) ≫ (I).hom = J :=
  PolygonPinching.nodes_polygonIso Q (2 * s + 4) (by omega) N J H

/-- Every entire projective component retains the original equation-level morphism. -/
@[reassoc] theorem coefficientShearResiduePolygonIso_component (i : Fin (2 * s + 4)) :
    (PolygonPinching.componentι Q (2 * s + 4) i).left ≫
      (PolygonAtlas.normalization Q (2 * s + 4)).left ≫ (I).hom.left = C i := by
  have h := congrArg (fun f => f.left)
    (coefficientShearResiduePolygonIso_normalization
      hπ hm data s hs he hstart h3 h4 h6 h6next hc)
  change (PolygonPinching.componentι Q (2 * s + 4) i).left ≫
    (PolygonAtlas.normalization Q (2 * s + 4) ≫ (I).hom).left = C i
  rw [h, coefficientShearResidueCycleCoproduct_ι]

end FLT.Mazur.WeierstrassDividedDepth
