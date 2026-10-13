/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCycleEndpoints

/-!
# Actual node coproduct and pinching cocone at zero-start strict depth

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
  (hm : maximalIdeal R = Ideal.span {π}) {n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (0 + (s + 1)) < depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "d" => data ⟨1, by omega⟩
local notation "hres" => nodalDepth_residue_uniformizer hm
local notation "F" => coefficientShearResidueExteriorLift hπ data (s + 1) hs d
  (by dsimp; omega) hres a
local notation "B" => coefficientShearResidueStrictAdjacentBranch
  hπ hm data s hs hk h3 h4 h6 hc
local notation "ρ" => ProjectiveLine.endpointReversal Q

local notation "C" => coefficientShearResidueStrictZeroCycleComponent
  hπ hm data s hs hk h3 h4 h6 hc

/-- The original node at a cyclic position, as an actual section of the final model. -/
def coefficientShearResidueStrictZeroCycleNode (i : Fin (2 * s + 3)) :
    Spec (.of Q) ⟶ coefficientShearGlued hπ data Q r (s + 1) hs :=
  ProjectiveLine.zero Q ≫ C i
local notation "N" => coefficientShearResidueStrictZeroCycleNode
  hπ hm data s hs hk h3 h4 h6 hc

/-- Each actual node is a section over the original residue field. -/
@[reassoc] theorem coefficientShearResidueStrictZeroCycleNode_structure (i : Fin (2 * s + 3)) :
    N i ≫ g = 𝟙 _ := by
  rw [coefficientShearResidueStrictZeroCycleNode, Category.assoc,
    coefficientShearResidueStrictZeroCycleComponent_structure, ProjectiveLine.zero_toBase]

/-- The other actual branch has the same node section, including the exterior wrap. -/
@[reassoc] theorem coefficientShearResidueStrictZeroCycleNode_infinity (i : Fin (2 * s + 3)) :
    ProjectiveLine.infinity Q ≫ C (PolygonPinching.next (by omega) i) = N i :=
  (coefficientShearResidueStrictZeroCycleComponent_endpoints
    hπ hm data s hs hk h3 h4 h6 hc i).symm

/-- The complete original node coproduct as a morphism over the residue field. -/
def coefficientShearResidueStrictZeroCycleNodes :
    PolygonPinching.nodes Q (2 * s + 3) ⟶ Over.mk g :=
  Sigma.desc fun i => Over.homMk (N i) (coefficientShearResidueStrictZeroCycleNode_structure
    hπ hm data s hs hk h3 h4 h6 hc i)
local notation "D" => coefficientShearResidueStrictZeroCycleNodes
  hπ hm data s hs hk h3 h4 h6 hc
local notation "M" => coefficientShearResidueStrictZeroCycleCoproduct
  hπ hm data s hs hk h3 h4 h6 hc

/-- Every node summand retains its original actual section. -/
@[reassoc] theorem coefficientShearResidueStrictZeroCycleNodes_ι (i : Fin (2 * s + 3)) :
    (PolygonPinching.nodeι Q (2 * s + 3) i).left ≫ (D).left = N i := by
  change (PolygonPinching.nodeι Q (2 * s + 3) i ≫ D).left = _
  rw [PolygonPinching.nodeι, coefficientShearResidueStrictZeroCycleNodes, Sigma.ι_comp_desc]
  rfl

/-- The actual full component and node coproducts satisfy the entire pinching square. -/
theorem coefficientShearResidueStrictZeroCycleCoproduct_cocone :
    PolygonPinching.toComponents Q (2 * s + 3) (by omega) ≫ M =
      PolygonPinching.toNodes Q (2 * s + 3) ≫ D := by
  apply Sigma.hom_ext
  rintro ⟨i, b⟩
  change PolygonPinching.branchι Q (2 * s + 3) i b ≫ _ =
    PolygonPinching.branchι Q (2 * s + 3) i b ≫ _
  cases b
  · rw [PolygonPinching.branchι_toComponents_zero_assoc,
      PolygonPinching.branchι_toNodes_assoc]
    apply Over.OverMorphism.ext
    change ProjectiveLine.zero Q ≫
      (PolygonPinching.componentι Q (2 * s + 3) i).left ≫ (M).left =
        (PolygonPinching.nodeι Q (2 * s + 3) i).left ≫ (D).left
    rw [coefficientShearResidueStrictZeroCycleCoproduct_ι,
      coefficientShearResidueStrictZeroCycleNodes_ι]
    rfl
  · rw [PolygonPinching.branchι_toComponents_infinity_assoc,
      PolygonPinching.branchι_toNodes_assoc]
    apply Over.OverMorphism.ext
    change ProjectiveLine.infinity Q ≫
      (PolygonPinching.componentι Q (2 * s + 3) (PolygonPinching.next (by omega) i)).left ≫
        (M).left = (PolygonPinching.nodeι Q (2 * s + 3) i).left ≫ (D).left
    rw [coefficientShearResidueStrictZeroCycleCoproduct_ι,
      coefficientShearResidueStrictZeroCycleNodes_ι,
      coefficientShearResidueStrictZeroCycleNode_infinity]

/-- The actual pinching cocone, with its already constructed complete component map. -/
def coefficientShearResidueStrictZeroCyclePushoutCocone :
    PushoutCocone (PolygonPinching.toComponents Q (2 * s + 3) (by omega))
      (PolygonPinching.toNodes Q (2 * s + 3)) :=
  PushoutCocone.mk M D (coefficientShearResidueStrictZeroCycleCoproduct_cocone
    hπ hm data s hs hk h3 h4 h6 hc)

end FLT.Mazur.WeierstrassDividedDepth
