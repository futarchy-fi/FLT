/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantOpenFiniteRelation
public import FLT.Mazur.AffineProjectiveRelationNormNeighborhood

/-!
# Original invariant principal neighborhoods on finite invariant affine domains

Geometry supplies finite-projective coordinates on the whole restricted
relation. Its constructed equivalence operations then give actual invariant
norm scalars and principal neighborhoods, without a global source basis.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.InvariantOpenRelationDiagram
open SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} {D A : Over S} (p q : D ⟶ A)
  (e : CategoryTheory.EquivalenceRelation p.left q.left)
  [Flat p.left] [LocallyOfFinitePresentation p.left]
  (U : A.left.Opens) (hU : p.left ⁻¹ᵁ U = q.left ⁻¹ᵁ U)
  (hf : U ≤ finiteTargetOpen p.left) (ha : IsAffineOpen U)

include e hf ha in
/-- Actual original invariant scalars refine whole-orbit opens in a finite affine domain. -/
theorem exists_invariantPrincipal_on_finiteDomain (W : (source U).left.Opens)
    (x : (source U).left)
    (hW : ∀ z : (relation p U).left, (fst p U).left z = x →
      (snd p q U hU).left z ∈ W) :
    ∃ s : Γ((source U).left, ⊤),
      (fst p U).left.appTop s = (snd p q U hU).left.appTop s ∧
      x ∈ (source U).left.basicOpen s ∧ (source U).left.basicOpen s ≤ W := by
  let _ : IsAffine (source U).left := ha
  let _ := relation_affine_of_le_finiteTarget p U hf ha
  let _ := fst_finite_of_le_finiteTarget p U hf
  exact AffineLocallyFreeRelationNorm.exists_invariant_principal_of_finite_projective
    (fst p U).left (snd p q U hU).left (schemeEquivalence p q e U hU) W x hW
    (fst p U).left.finite_appTop (fst_projective_of_le_finiteTarget p U hf ha)

end FLT.Mazur.InvariantOpenRelationDiagram
