/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueCycleEndpoints

/-!
# The actual residue node coproduct and pinching cocone

The complete component and node coproducts form the specified cyclic span in
the original residue-tangent target. A universal property is a further obligation.
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

local notation "C" => coefficientShearResidueCycleComponent
  hπ hm data s hs he hstart h3 h4 h6 h6next hc
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)
local notation "P" => ProjectiveLine.coefficientMap (f).toRingHom
local notation "e" => data ⟨s + 1, Nat.lt_succ_of_le hs⟩
local notation "cunit" => nodalDepth_tangent_constant_isUnit hm e he h6next

/-- The original node at a cyclic position, as an actual section of the final model. -/
def coefficientShearResidueCycleNode (i : Fin (2 * s + 4)) :
    Spec (.of Q) ⟶ coefficientShearGlued hπ data Q r (s + 1) hs :=
  ProjectiveLine.zero Q ≫ C i
local notation "N" => coefficientShearResidueCycleNode
  hπ hm data s hs he hstart h3 h4 h6 h6next hc

/-- Each actual node is a section over the original residue field. -/
@[reassoc] theorem coefficientShearResidueCycleNode_structure (i : Fin (2 * s + 4)) :
    N i ≫ g = 𝟙 _ := by
  rw [coefficientShearResidueCycleNode, Category.assoc,
    coefficientShearResidueCycleComponent_structure, ProjectiveLine.zero_toBase]

/-- The other actual branch has the same node section, including the exterior wrap. -/
@[reassoc] theorem coefficientShearResidueCycleNode_infinity (i : Fin (2 * s + 4)) :
    ProjectiveLine.infinity Q ≫ C (PolygonPinching.next (by omega) i) = N i :=
  (coefficientShearResidueCycleComponent_endpoints
    hπ hm data s hs he hstart h3 h4 h6 h6next hc i).symm

/-- The complete original node coproduct as a morphism over the residue field. -/
def coefficientShearResidueCycleNodes :
    PolygonPinching.nodes Q (2 * s + 4) ⟶ Over.mk g :=
  Sigma.desc fun i => Over.homMk (N i) (coefficientShearResidueCycleNode_structure
    hπ hm data s hs he hstart h3 h4 h6 h6next hc i)
local notation "D" => coefficientShearResidueCycleNodes
  hπ hm data s hs he hstart h3 h4 h6 h6next hc
local notation "M" => coefficientShearResidueCycleCoproduct
  hπ hm data s hs he hstart h3 h4 h6 h6next hc

/-- Every node summand retains its original actual section. -/
@[reassoc] theorem coefficientShearResidueCycleNodes_ι (i : Fin (2 * s + 4)) :
    (PolygonPinching.nodeι Q (2 * s + 4) i).left ≫ (D).left = N i := by
  change (PolygonPinching.nodeι Q (2 * s + 4) i ≫ D).left = _
  rw [PolygonPinching.nodeι, coefficientShearResidueCycleNodes, Sigma.ι_comp_desc]
  rfl

/-- The actual full component and node coproducts satisfy the entire pinching square. -/
theorem coefficientShearResidueCycleCoproduct_cocone :
    PolygonPinching.toComponents Q (2 * s + 4) (by omega) ≫ M =
      PolygonPinching.toNodes Q (2 * s + 4) ≫ D := by
  apply Sigma.hom_ext
  rintro ⟨i, b⟩
  change PolygonPinching.branchι Q (2 * s + 4) i b ≫ _ =
    PolygonPinching.branchι Q (2 * s + 4) i b ≫ _
  cases b
  · rw [PolygonPinching.branchι_toComponents_zero_assoc,
      PolygonPinching.branchι_toNodes_assoc]
    apply Over.OverMorphism.ext
    change ProjectiveLine.zero Q ≫
      (PolygonPinching.componentι Q (2 * s + 4) i).left ≫ (M).left =
        (PolygonPinching.nodeι Q (2 * s + 4) i).left ≫ (D).left
    rw [coefficientShearResidueCycleCoproduct_ι, coefficientShearResidueCycleNodes_ι]
    rfl
  · rw [PolygonPinching.branchι_toComponents_infinity_assoc,
      PolygonPinching.branchι_toNodes_assoc]
    apply Over.OverMorphism.ext
    change ProjectiveLine.infinity Q ≫
      (PolygonPinching.componentι Q (2 * s + 4) (PolygonPinching.next (by omega) i)).left ≫
        (M).left = (PolygonPinching.nodeι Q (2 * s + 4) i).left ≫ (D).left
    rw [coefficientShearResidueCycleCoproduct_ι, coefficientShearResidueCycleNodes_ι,
      coefficientShearResidueCycleNode_infinity]

/-- The actual pinching cocone, with its already constructed complete component map. -/
def coefficientShearResidueCyclePushoutCocone :
    PushoutCocone (PolygonPinching.toComponents Q (2 * s + 4) (by omega))
      (PolygonPinching.toNodes Q (2 * s + 4)) :=
  PushoutCocone.mk M D (coefficientShearResidueCycleCoproduct_cocone
    hπ hm data s hs he hstart h3 h4 h6 h6next hc)

end FLT.Mazur.WeierstrassDividedDepth
