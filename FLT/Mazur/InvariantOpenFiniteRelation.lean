/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantOpenRelationEquivalence
public import FLT.Mazur.SchemeFiniteTargetRestriction
public import FLT.Mazur.FiniteFlatGlobalSections

/-!
# Finite-projective geometry on actual invariant finite domains

An invariant open inside the exact finite locus retains the entire original
relation. Its first endpoint is finite, and on an affine source its original
coordinate algebra is finite projective by flat finite presentation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.InvariantOpenRelationDiagram
open SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} {D A : Over S} (p : D ⟶ A)
  (U : A.left.Opens) (hU : U ≤ finiteTargetOpen p.left)

include hU in
/-- The entire first endpoint is finite on any invariant domain in the exact finite locus. -/
theorem fst_finite_of_le_finiteTarget : IsFinite (fst p U).left := by
  change IsFinite (p.left.resLE U _ le_rfl)
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact finite_restrict_of_le_finiteTarget p.left U hU

include hU in
/-- The whole original relation above an affine finite target domain is affine. -/
theorem relation_affine_of_le_finiteTarget (ha : IsAffineOpen U) :
    IsAffine (relation p U).left := by
  let _ : IsAffine (source U).left := ha
  let _ := fst_finite_of_le_finiteTarget p U hU
  exact isAffine_of_isAffineHom (fst p U).left

variable [Flat p.left] [LocallyOfFinitePresentation p.left]

include hU in
/-- Flat finite presentation constructs projectivity of the actual restricted coordinates. -/
theorem fst_projective_of_le_finiteTarget (ha : IsAffineOpen U) :
    let _ := (fst p U).left.appTop.hom.toAlgebra
    Module.Projective Γ((source U).left, ⊤) Γ((relation p U).left, ⊤) := by
  let _ : IsAffine (source U).left := ha
  let _ := relation_affine_of_le_finiteTarget p U hU ha
  let _ := fst_finite_of_le_finiteTarget p U hU
  let _ : Flat (fst p U).left := by
    change Flat (p.left.resLE U _ le_rfl)
    infer_instance
  let _ : LocallyOfFinitePresentation (fst p U).left := by
    change LocallyOfFinitePresentation (p.left.resLE U _ le_rfl)
    infer_instance
  exact FCurve.finiteFlat_appTop_projective (fst p U).left

end FLT.Mazur.InvariantOpenRelationDiagram
