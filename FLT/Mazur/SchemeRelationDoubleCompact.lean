/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationDoubleRestriction
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Quasicompactness of full two-endpoint relations

A quasicompact source map preserves quasicompactness of the entire original
relation when both endpoints are lifted. No endpoint surjectivity, stable
open, or restriction to a set of closed points is required.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A X Y : Scheme.{u}} (p q : A ⟶ X) (k : Y ⟶ X)

/-- The map retaining the original arrow is quasicompact if the source map is. -/
instance arrow_quasiCompact [QuasiCompact k] : QuasiCompact (arrow p q k) := by
  unfold arrow
  exact quasiCompact_comp _ _

/-- Lifting both endpoints retains quasicompactness of the full relation. -/
instance doubleDomain_compactSpace [CompactSpace A] [QuasiCompact k] :
    CompactSpace (doubleDomain p q k) :=
  QuasiCompact.compactSpace_of_compactSpace (arrow p q k)

/-- Affine source charts preserve quasicompactness over an affine original source. -/
theorem doubleDomain_compactSpace_of_affine [CompactSpace A] [IsAffine X] [IsAffine Y] :
    CompactSpace (doubleDomain p q k) := by
  infer_instance

end FLT.Mazur.SchemeRelationRestriction
