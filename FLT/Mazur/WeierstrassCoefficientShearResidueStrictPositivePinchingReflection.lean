/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveCycleReflection
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveCycleNodes
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveCoproductHomExt
public import FLT.Mazur.WeierstrassCoefficientShearResidueSourceInvolution
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveCycleReflection

/-!
# Semilinear reflection of the strict positive-start pinching diagram

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
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)
local notation "c" => fun _ : Fin (2 * s + 5) => (1 : Qˣ)
local notation "N" => coefficientShearResidueStrictPositiveCycleCoproduct
  hπ hm data s hs hk hstart h3 h4 h6 hc
local notation "J" => coefficientShearResidueStrictPositiveCycleNodes
  hπ hm data s hs hk hstart h3 h4 h6 hc
local notation "q" => Spec.map (CommRingCat.ofHom (f).toRingHom)

local notation "S" => PolygonPinching.semilinearScaledComponents (f).toRingHom c
local notation "D" => PolygonPinching.semilinearReflectionNodes (n := 2 * s + 5) (f).toRingHom
local notation "B" => PolygonPinching.semilinearReflectionBranches
  (n := 2 * s + 5) (f).toRingHom

/-- The full strict normalization intertwines the original coefficient conjugation. -/
@[reassoc] theorem coefficientShearResidueStrictPositiveCycleCoproduct_conjugation :
    (N).left ≫ σ = S ≫ (N).left := by
  apply OverCoproductScheme.hom_ext (fun _ : Fin (2 * s + 5) => PolygonPinching.component Q)
  intro i
  change (PolygonPinching.componentι Q (2 * s + 5) i).left ≫ _ =
    (PolygonPinching.componentι Q (2 * s + 5) i).left ≫ _
  rw [coefficientShearResidueStrictPositiveCycleCoproduct_ι_assoc,
    PolygonPinching.componentι_semilinearScaledComponents_assoc,
    coefficientShearResidueStrictPositiveCycleCoproduct_ι]
  simpa only [PolygonPinching.semilinearScaledParameter,
    ProjectiveLine.scaledEndpointReversal, ProjectiveLine.scaling_one,
    Category.comp_id, Category.assoc] using
    coefficientShearResidueStrictPositiveCycleComponent_reflection
      hπ hm data s hs hk hstart h3 h4 h6 hc i

/-- Every full node section retains the shifted reflected index and coefficient map. -/
@[reassoc] theorem coefficientShearResidueStrictPositiveCycleNode_conjugation
    (i : Fin (2 * s + 5)) :
    coefficientShearResidueStrictPositiveCycleNode hπ hm data s hs hk hstart h3 h4 h6 hc i ≫ σ =
      q ≫ coefficientShearResidueStrictPositiveCycleNode
        hπ hm data s hs hk hstart h3 h4 h6 hc (PolygonPinching.reflectNodeIndex i) := by
  rw [coefficientShearResidueStrictPositiveCycleNode, Category.assoc,
    coefficientShearResidueStrictPositiveCycleComponent_reflection]
  rw [ProjectiveLine.zero_coefficientMap_assoc,
    ProjectiveLine.zero_endpointReversal_assoc,
    ← PolygonPinching.next_reflectNodeIndex (by omega) i,
    coefficientShearResidueStrictPositiveCycleNode_infinity]

/-- The entire original node coproduct intertwines the same residue conjugation. -/
@[reassoc] theorem coefficientShearResidueStrictPositiveCycleNodes_conjugation :
    (J).left ≫ σ = D ≫ (J).left := by
  apply OverCoproductScheme.hom_ext (fun _ : Fin (2 * s + 5) => PolygonPinching.point Q)
  intro i
  change (PolygonPinching.nodeι Q (2 * s + 5) i).left ≫ _ =
    (PolygonPinching.nodeι Q (2 * s + 5) i).left ≫ _
  rw [coefficientShearResidueStrictPositiveCycleNodes_ι_assoc,
    PolygonPinching.nodeι_semilinearReflectionNodes_assoc,
    coefficientShearResidueStrictPositiveCycleNodes_ι,
    coefficientShearResidueStrictPositiveCycleNode_conjugation]

omit [IsDomain R] [IsBezout R] in
/-- Both original branches retain the actual normalization leg under scaled conjugation. -/
theorem coefficientShearResidueStrictPositiveSourceReflection_components :
    B ≫ (PolygonPinching.toComponents Q (2 * s + 5) (by omega)).left =
      (PolygonPinching.toComponents Q (2 * s + 5) (by omega)).left ≫ S :=
  PolygonPinching.semilinearScaled_toComponents (f).toRingHom c (by omega)

omit [IsDomain R] [IsBezout R] in
/-- The exact original branch-to-node leg retains its semilinear reflection. -/
theorem coefficientShearResidueStrictPositiveSourceReflection_nodes :
    B ≫ (PolygonPinching.toNodes Q (2 * s + 5)).left =
      (PolygonPinching.toNodes Q (2 * s + 5)).left ≫ D :=
  PolygonPinching.semilinearReflection_toNodes (f).toRingHom

omit [IsDomain R] [IsBezout R] in
/-- Applying the complete coefficient-one normalization reflection twice is the identity. -/
@[reassoc] theorem coefficientShearResidueStrictPositiveSourceReflection_involutive :
    S ≫ S = 𝟙 _ :=
  PolygonPinching.semilinearScaledComponents_involutive (f).toRingHom
    (tangentResidueConjugation_comp_self (W := W)) c (fun _ => map_one _) (fun _ => rfl)

omit [IsDomain R] [IsBezout R] in
/-- The actual reflected node coefficients are restored after two conjugations. -/
@[reassoc] theorem coefficientShearResidueStrictPositiveNodesReflection_involutive :
    D ≫ D = 𝟙 _ :=
  PolygonPinching.semilinearReflectionNodes_involutive (f).toRingHom
    (tangentResidueConjugation_comp_self (W := W))

omit [IsDomain R] [IsBezout R] in
/-- Both original branch labels and their coefficient points are restored. -/
@[reassoc] theorem coefficientShearResidueStrictPositiveBranchesReflection_involutive :
    B ≫ B = 𝟙 _ :=
  PolygonPinching.semilinearReflectionBranches_involutive (f).toRingHom
    (tangentResidueConjugation_comp_self (W := W))

/-- The whole normalization reflection uniquely determines the actual target conjugation. -/
theorem coefficientShearResidueStrictPositiveReflection_unique
    (u : coefficientShearGlued hπ data
      (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
      (AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))) (s + 1) hs ⟶
      coefficientShearGlued hπ data
        (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
        (AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))) (s + 1) hs)
    (hu : (N).left ≫ u = S ≫ (N).left) : u = σ := by
  apply coefficientShearResidueStrictPositiveCycleCoproduct_hom_ext
    hπ hm data s hs hk hstart h3 h4 h6 hc
  exact hu.trans (coefficientShearResidueStrictPositiveCycleCoproduct_conjugation
    hπ hm data s hs hk hstart h3 h4 h6 hc).symm

end FLT.Mazur.WeierstrassDividedDepth
