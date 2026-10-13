/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroSourceReflection
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroCycleNodes
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroSourceReflection

/-!
# Scaled semilinear reflection of the start-zero pinching diagram

The entire original component and node coproducts intertwine the actual residue
conjugation. The branch exchange retains both original legs of the source span.
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
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)
local notation "c" => coefficientShearResidueZeroReflectionScale hm data s hs he h6next
local notation "N" => coefficientShearResidueZeroEqualityCycleCoproduct
  hπ hm data s hs he h3 h4 h6next hc
local notation "J" => coefficientShearResidueZeroEqualityCycleNodes
  hπ hm data s hs he h3 h4 h6next hc
local notation "q" => Spec.map (CommRingCat.ofHom (f).toRingHom)

local notation "S" => PolygonPinching.semilinearScaledComponents (f).toRingHom c
local notation "D" => PolygonPinching.semilinearReflectionNodes (n := 2 * s + 2) (f).toRingHom
local notation "B" => PolygonPinching.semilinearReflectionBranches
  (n := 2 * s + 2) (f).toRingHom

/-- Every full node section retains the shifted reflected index and coefficient map. -/
@[reassoc] theorem coefficientShearResidueZeroEqualityCycleNode_conjugation (i : Fin (2 * s + 2)) :
    coefficientShearResidueZeroEqualityCycleNode hπ hm data s hs he h3 h4 h6next hc i ≫ σ =
      q ≫ coefficientShearResidueZeroEqualityCycleNode
        hπ hm data s hs he h3 h4 h6next hc (PolygonPinching.reflectNodeIndex i) := by
  rw [coefficientShearResidueZeroEqualityCycleNode, Category.assoc,
    coefficientShearResidueZeroEqualityCycleComponent_reflection]
  change ProjectiveLine.zero Q ≫ PolygonPinching.semilinearScaledParameter
    (f).toRingHom c i ≫ C (PolygonPinching.reflectIndex i) = _
  rw [PolygonPinching.semilinearScaledParameter_zero_assoc,
    ← PolygonPinching.next_reflectNodeIndex (by omega) i,
    coefficientShearResidueZeroEqualityCycleNode_infinity]

/-- The entire original node coproduct intertwines the same residue conjugation. -/
@[reassoc] theorem coefficientShearResidueZeroEqualityCycleNodes_conjugation :
    (J).left ≫ σ = D ≫ (J).left := by
  apply OverCoproductScheme.hom_ext (fun _ : Fin (2 * s + 2) => PolygonPinching.point Q)
  intro i
  change (PolygonPinching.nodeι Q (2 * s + 2) i).left ≫ _ =
    (PolygonPinching.nodeι Q (2 * s + 2) i).left ≫ _
  rw [coefficientShearResidueZeroEqualityCycleNodes_ι_assoc,
    PolygonPinching.nodeι_semilinearReflectionNodes_assoc,
    coefficientShearResidueZeroEqualityCycleNodes_ι,
    coefficientShearResidueZeroEqualityCycleNode_conjugation]

omit [IsDomain R] [IsBezout R] in
/-- Both original branches retain the actual normalization leg under scaled conjugation. -/
theorem coefficientShearResidueZeroSourceReflection_components :
    B ≫ (PolygonPinching.toComponents Q (2 * s + 2) (by omega)).left =
      (PolygonPinching.toComponents Q (2 * s + 2) (by omega)).left ≫ S :=
  PolygonPinching.semilinearScaled_toComponents (f).toRingHom c (by omega)

omit [IsDomain R] [IsBezout R] in
/-- The exact original branch-to-node leg retains its semilinear reflection. -/
theorem coefficientShearResidueZeroSourceReflection_nodes :
    B ≫ (PolygonPinching.toNodes Q (2 * s + 2)).left =
      (PolygonPinching.toNodes Q (2 * s + 2)).left ≫ D :=
  PolygonPinching.semilinearReflection_toNodes (f).toRingHom

end FLT.Mazur.WeierstrassDividedDepth
