/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueReflectionParameters
public import FLT.Mazur.WeierstrassCoefficientShearResidueCycleNodes
import all FLT.Mazur.WeierstrassCoefficientShearResidueReflectionParameters

/-!
# Scaled semilinear reflection of the full original residue pinching diagram

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

local notation "c" => coefficientShearResidueReflectionScale hm data s hs he h6next
local notation "p" => coefficientShearResidueReflectionParameter hm data s hs he h6next
local notation "N" => coefficientShearResidueCycleCoproduct
  hπ hm data s hs he hstart h3 h4 h6 h6next hc
local notation "J" => coefficientShearResidueCycleNodes
  hπ hm data s hs he hstart h3 h4 h6 h6next hc
local notation "q" => Spec.map (CommRingCat.ofHom (f).toRingHom)

/-- The full scaled semilinear reflection on the original normalization source. -/
def coefficientShearResidueSourceReflection :=
  PolygonPinching.semilinearScaledComponents (f).toRingHom c
local notation "S" => coefficientShearResidueSourceReflection hm data s hs he h6next
local notation "D" => PolygonPinching.semilinearReflectionNodes (n := 2 * s + 4) (f).toRingHom
local notation "B" => PolygonPinching.semilinearReflectionBranches
  (n := 2 * s + 4) (f).toRingHom

/-- The entire original normalization coproduct intertwines the actual residue conjugation. -/
@[reassoc] theorem coefficientShearResidueCycleCoproduct_conjugation :
    (N).left ≫ σ = S ≫ (N).left := by
  apply OverCoproductScheme.hom_ext (fun _ : Fin (2 * s + 4) => PolygonPinching.component Q)
  intro i
  change (PolygonPinching.componentι Q (2 * s + 4) i).left ≫ _ =
    (PolygonPinching.componentι Q (2 * s + 4) i).left ≫ _
  rw [coefficientShearResidueCycleCoproduct_ι_assoc,
    coefficientShearResidueSourceReflection,
    PolygonPinching.componentι_semilinearScaledComponents_assoc,
    coefficientShearResidueCycleCoproduct_ι]
  exact coefficientShearResidueCycleComponent_reflection
    hπ hm data s hs he hstart h3 h4 h6 h6next hc i

/-- Every full node section retains the shifted reflected index and coefficient map. -/
@[reassoc] theorem coefficientShearResidueCycleNode_conjugation (i : Fin (2 * s + 4)) :
    coefficientShearResidueCycleNode hπ hm data s hs he hstart h3 h4 h6 h6next hc i ≫ σ =
      q ≫ coefficientShearResidueCycleNode
        hπ hm data s hs he hstart h3 h4 h6 h6next hc (PolygonPinching.reflectNodeIndex i) := by
  rw [coefficientShearResidueCycleNode, Category.assoc,
    coefficientShearResidueCycleComponent_reflection]
  change ProjectiveLine.zero Q ≫ PolygonPinching.semilinearScaledParameter
    (f).toRingHom c i ≫ C (PolygonPinching.reflectIndex i) = _
  rw [PolygonPinching.semilinearScaledParameter_zero_assoc,
    ← PolygonPinching.next_reflectNodeIndex (by omega) i,
    coefficientShearResidueCycleNode_infinity]

/-- The entire original node coproduct intertwines the same residue conjugation. -/
@[reassoc] theorem coefficientShearResidueCycleNodes_conjugation :
    (J).left ≫ σ = D ≫ (J).left := by
  apply OverCoproductScheme.hom_ext (fun _ : Fin (2 * s + 4) => PolygonPinching.point Q)
  intro i
  change (PolygonPinching.nodeι Q (2 * s + 4) i).left ≫ _ =
    (PolygonPinching.nodeι Q (2 * s + 4) i).left ≫ _
  rw [coefficientShearResidueCycleNodes_ι_assoc,
    PolygonPinching.nodeι_semilinearReflectionNodes_assoc,
    coefficientShearResidueCycleNodes_ι, coefficientShearResidueCycleNode_conjugation]

omit [IsDomain R] [IsBezout R] in
/-- Both original branches retain the actual normalization leg under scaled conjugation. -/
theorem coefficientShearResidueSourceReflection_components :
    B ≫ (PolygonPinching.toComponents Q (2 * s + 4) (by omega)).left =
      (PolygonPinching.toComponents Q (2 * s + 4) (by omega)).left ≫ S :=
  PolygonPinching.semilinearScaled_toComponents (f).toRingHom c (by omega)

omit [IsDomain R] [IsBezout R] in
/-- The exact original branch-to-node leg retains its semilinear reflection. -/
theorem coefficientShearResidueSourceReflection_nodes :
    B ≫ (PolygonPinching.toNodes Q (2 * s + 4)).left =
      (PolygonPinching.toNodes Q (2 * s + 4)).left ≫ D :=
  PolygonPinching.semilinearReflection_toNodes (f).toRingHom

end FLT.Mazur.WeierstrassDividedDepth
