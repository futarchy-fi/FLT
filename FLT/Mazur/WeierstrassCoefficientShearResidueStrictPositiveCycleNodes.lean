/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveCycleEndpoints

/-!
# Actual node coproduct and pinching cocone at positive-start strict depth

The complete original components and their actual node sections form the
specified odd pinching diagram. Its universal property is a separate obligation.
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
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth)
  (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "hres" => nodalDepth_residue_uniformizer hm
local notation "F" => coefficientShearResidueExteriorLift hπ data (s + 1) hs d
  (by dsimp; omega) hres a
local notation "B" => coefficientShearResidueStrictPositiveBranch
  hπ hm data s hs hk h3 h4 h6 hc hstart
local notation "ρ" => ProjectiveLine.endpointReversal Q

local notation "C" => coefficientShearResidueStrictPositiveCycleComponent
  hπ hm data s hs hk hstart h3 h4 h6 hc

/-- The original node at a cyclic position, as an actual section of the final model. -/
def coefficientShearResidueStrictPositiveCycleNode (i : Fin (2 * s + 5)) :
    Spec (.of Q) ⟶ coefficientShearGlued hπ data Q r (s + 1) hs :=
  ProjectiveLine.zero Q ≫ C i
local notation "N" => coefficientShearResidueStrictPositiveCycleNode
  hπ hm data s hs hk hstart h3 h4 h6 hc

/-- Each actual node is a section over the original residue field. -/
@[reassoc] theorem coefficientShearResidueStrictPositiveCycleNode_structure (i : Fin (2 * s + 5)) :
    N i ≫ g = 𝟙 _ := by
  rw [coefficientShearResidueStrictPositiveCycleNode, Category.assoc,
    coefficientShearResidueStrictPositiveCycleComponent_structure, ProjectiveLine.zero_toBase]

/-- The other actual branch has the same node section, including the exterior wrap. -/
@[reassoc] theorem coefficientShearResidueStrictPositiveCycleNode_infinity (i : Fin (2 * s + 5)) :
    ProjectiveLine.infinity Q ≫ C (PolygonPinching.next (by omega) i) = N i :=
  (coefficientShearResidueStrictPositiveCycleComponent_endpoints
    hπ hm data s hs hk hstart h3 h4 h6 hc i).symm

/-- The complete original node coproduct as a morphism over the residue field. -/
def coefficientShearResidueStrictPositiveCycleNodes :
    PolygonPinching.nodes Q (2 * s + 5) ⟶ Over.mk g :=
  Sigma.desc fun i => Over.homMk (N i) (coefficientShearResidueStrictPositiveCycleNode_structure
    hπ hm data s hs hk hstart h3 h4 h6 hc i)
local notation "D" => coefficientShearResidueStrictPositiveCycleNodes
  hπ hm data s hs hk hstart h3 h4 h6 hc
local notation "M" => coefficientShearResidueStrictPositiveCycleCoproduct
  hπ hm data s hs hk hstart h3 h4 h6 hc

/-- Every node summand retains its original actual section. -/
@[reassoc] theorem coefficientShearResidueStrictPositiveCycleNodes_ι (i : Fin (2 * s + 5)) :
    (PolygonPinching.nodeι Q (2 * s + 5) i).left ≫ (D).left = N i := by
  change (PolygonPinching.nodeι Q (2 * s + 5) i ≫ D).left = _
  rw [PolygonPinching.nodeι, coefficientShearResidueStrictPositiveCycleNodes, Sigma.ι_comp_desc]
  rfl

/-- The actual full component and node coproducts satisfy the entire pinching square. -/
theorem coefficientShearResidueStrictPositiveCycleCoproduct_cocone :
    PolygonPinching.toComponents Q (2 * s + 5) (by omega) ≫ M =
      PolygonPinching.toNodes Q (2 * s + 5) ≫ D := by
  apply Sigma.hom_ext
  rintro ⟨i, b⟩
  change PolygonPinching.branchι Q (2 * s + 5) i b ≫ _ =
    PolygonPinching.branchι Q (2 * s + 5) i b ≫ _
  cases b
  · rw [PolygonPinching.branchι_toComponents_zero_assoc,
      PolygonPinching.branchι_toNodes_assoc]
    apply Over.OverMorphism.ext
    change ProjectiveLine.zero Q ≫
      (PolygonPinching.componentι Q (2 * s + 5) i).left ≫ (M).left =
        (PolygonPinching.nodeι Q (2 * s + 5) i).left ≫ (D).left
    rw [coefficientShearResidueStrictPositiveCycleCoproduct_ι,
      coefficientShearResidueStrictPositiveCycleNodes_ι]
    rfl
  · rw [PolygonPinching.branchι_toComponents_infinity_assoc,
      PolygonPinching.branchι_toNodes_assoc]
    apply Over.OverMorphism.ext
    change ProjectiveLine.infinity Q ≫
      (PolygonPinching.componentι Q (2 * s + 5) (PolygonPinching.next (by omega) i)).left ≫
        (M).left = (PolygonPinching.nodeι Q (2 * s + 5) i).left ≫ (D).left
    rw [coefficientShearResidueStrictPositiveCycleCoproduct_ι,
      coefficientShearResidueStrictPositiveCycleNodes_ι,
      coefficientShearResidueStrictPositiveCycleNode_infinity]

/-- The actual pinching cocone, with its already constructed complete component map. -/
def coefficientShearResidueStrictPositiveCyclePushoutCocone :
    PushoutCocone (PolygonPinching.toComponents Q (2 * s + 5) (by omega))
      (PolygonPinching.toNodes Q (2 * s + 5)) :=
  PushoutCocone.mk M D (coefficientShearResidueStrictPositiveCycleCoproduct_cocone
    hπ hm data s hs hk hstart h3 h4 h6 hc)

end FLT.Mazur.WeierstrassDividedDepth
