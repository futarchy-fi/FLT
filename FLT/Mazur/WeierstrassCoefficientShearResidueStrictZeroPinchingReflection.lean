/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCycleReflection
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCycleNodes
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCoproductHomExt
public import FLT.Mazur.WeierstrassCoefficientShearResidueSourceInvolution
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCycleReflection

/-!
# Semilinear reflection of the strict zero-start pinching diagram

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
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (0 + (s + 1)) < depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "C" => coefficientShearResidueStrictZeroCycleComponent
  hπ hm data s hs hk h3 h4 h6 hc
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)
local notation "c" => fun _ : Fin (2 * s + 3) => (1 : Qˣ)
local notation "N" => coefficientShearResidueStrictZeroCycleCoproduct
  hπ hm data s hs hk h3 h4 h6 hc
local notation "J" => coefficientShearResidueStrictZeroCycleNodes
  hπ hm data s hs hk h3 h4 h6 hc
local notation "q" => Spec.map (CommRingCat.ofHom (f).toRingHom)

local notation "S" => PolygonPinching.semilinearScaledComponents (f).toRingHom c
local notation "D" => PolygonPinching.semilinearReflectionNodes (n := 2 * s + 3) (f).toRingHom
local notation "B" => PolygonPinching.semilinearReflectionBranches
  (n := 2 * s + 3) (f).toRingHom

/-- The full strict normalization intertwines the original coefficient conjugation. -/
@[reassoc] theorem coefficientShearResidueStrictZeroCycleCoproduct_conjugation :
    (N).left ≫ σ = S ≫ (N).left := by
  apply OverCoproductScheme.hom_ext (fun _ : Fin (2 * s + 3) => PolygonPinching.component Q)
  intro i
  change (PolygonPinching.componentι Q (2 * s + 3) i).left ≫ _ =
    (PolygonPinching.componentι Q (2 * s + 3) i).left ≫ _
  rw [coefficientShearResidueStrictZeroCycleCoproduct_ι_assoc,
    PolygonPinching.componentι_semilinearScaledComponents_assoc,
    coefficientShearResidueStrictZeroCycleCoproduct_ι]
  simpa only [PolygonPinching.semilinearScaledParameter,
    ProjectiveLine.scaledEndpointReversal, ProjectiveLine.scaling_one,
    Category.comp_id, Category.assoc] using
    coefficientShearResidueStrictZeroCycleComponent_reflection
      hπ hm data s hs hk h3 h4 h6 hc i

/-- Every full node section retains the shifted reflected index and coefficient map. -/
@[reassoc] theorem coefficientShearResidueStrictZeroCycleNode_conjugation (i : Fin (2 * s + 3)) :
    coefficientShearResidueStrictZeroCycleNode hπ hm data s hs hk h3 h4 h6 hc i ≫ σ =
      q ≫ coefficientShearResidueStrictZeroCycleNode
        hπ hm data s hs hk h3 h4 h6 hc (PolygonPinching.reflectNodeIndex i) := by
  rw [coefficientShearResidueStrictZeroCycleNode, Category.assoc,
    coefficientShearResidueStrictZeroCycleComponent_reflection]
  rw [ProjectiveLine.zero_coefficientMap_assoc,
    ProjectiveLine.zero_endpointReversal_assoc,
    ← PolygonPinching.next_reflectNodeIndex (by omega) i,
    coefficientShearResidueStrictZeroCycleNode_infinity]

/-- The entire original node coproduct intertwines the same residue conjugation. -/
@[reassoc] theorem coefficientShearResidueStrictZeroCycleNodes_conjugation :
    (J).left ≫ σ = D ≫ (J).left := by
  apply OverCoproductScheme.hom_ext (fun _ : Fin (2 * s + 3) => PolygonPinching.point Q)
  intro i
  change (PolygonPinching.nodeι Q (2 * s + 3) i).left ≫ _ =
    (PolygonPinching.nodeι Q (2 * s + 3) i).left ≫ _
  rw [coefficientShearResidueStrictZeroCycleNodes_ι_assoc,
    PolygonPinching.nodeι_semilinearReflectionNodes_assoc,
    coefficientShearResidueStrictZeroCycleNodes_ι,
    coefficientShearResidueStrictZeroCycleNode_conjugation]

omit [IsDomain R] [IsBezout R] in
/-- Both original branches retain the actual normalization leg under scaled conjugation. -/
theorem coefficientShearResidueStrictZeroSourceReflection_components :
    B ≫ (PolygonPinching.toComponents Q (2 * s + 3) (by omega)).left =
      (PolygonPinching.toComponents Q (2 * s + 3) (by omega)).left ≫ S :=
  PolygonPinching.semilinearScaled_toComponents (f).toRingHom c (by omega)

omit [IsDomain R] [IsBezout R] in
/-- The exact original branch-to-node leg retains its semilinear reflection. -/
theorem coefficientShearResidueStrictZeroSourceReflection_nodes :
    B ≫ (PolygonPinching.toNodes Q (2 * s + 3)).left =
      (PolygonPinching.toNodes Q (2 * s + 3)).left ≫ D :=
  PolygonPinching.semilinearReflection_toNodes (f).toRingHom

omit [IsDomain R] [IsBezout R] in
/-- Applying the complete coefficient-one normalization reflection twice is the identity. -/
@[reassoc] theorem coefficientShearResidueStrictZeroSourceReflection_involutive :
    S ≫ S = 𝟙 _ :=
  PolygonPinching.semilinearScaledComponents_involutive (f).toRingHom
    (tangentResidueConjugation_comp_self (W := W)) c (fun _ => map_one _) (fun _ => rfl)

omit [IsDomain R] [IsBezout R] in
/-- The actual reflected node coefficients are restored after two conjugations. -/
@[reassoc] theorem coefficientShearResidueStrictZeroNodesReflection_involutive :
    D ≫ D = 𝟙 _ :=
  PolygonPinching.semilinearReflectionNodes_involutive (f).toRingHom
    (tangentResidueConjugation_comp_self (W := W))

omit [IsDomain R] [IsBezout R] in
/-- Both original branch labels and their coefficient points are restored. -/
@[reassoc] theorem coefficientShearResidueStrictZeroBranchesReflection_involutive :
    B ≫ B = 𝟙 _ :=
  PolygonPinching.semilinearReflectionBranches_involutive (f).toRingHom
    (tangentResidueConjugation_comp_self (W := W))

/-- The whole normalization reflection uniquely determines the actual target conjugation. -/
theorem coefficientShearResidueStrictZeroReflection_unique
    (u : coefficientShearGlued hπ data
      (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
      (AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))) (s + 1) hs ⟶
      coefficientShearGlued hπ data
        (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
        (AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))) (s + 1) hs)
    (hu : (N).left ≫ u = S ≫ (N).left) : u = σ := by
  apply coefficientShearResidueStrictZeroCycleCoproduct_hom_ext
    hπ hm data s hs hk h3 h4 h6 hc
  exact hu.trans (coefficientShearResidueStrictZeroCycleCoproduct_conjugation
    hπ hm data s hs hk h3 h4 h6 hc).symm

end FLT.Mazur.WeierstrassDividedDepth
