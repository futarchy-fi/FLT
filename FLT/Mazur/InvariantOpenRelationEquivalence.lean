/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationInvariantRestriction
public import FLT.Mazur.InvariantOpenRelationDiagram

/-!
# Equivalence operations on the entire invariant open relation

The original equivalence operations restrict through the cartesian
first-endpoint square. Both independent endpoints and all original arrows
are retained on the invariant source domain.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.InvariantOpenRelationDiagram
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} {D A : Over S} (p q : D ⟶ A)
  (e : CategoryTheory.EquivalenceRelation p.left q.left)
  (U : A.left.Opens) (hU : p.left ⁻¹ᵁ U = q.left ⁻¹ᵁ U)

/-- The whole relation on an invariant domain is a constructed scheme equivalence relation. -/
def schemeEquivalence :
    CategoryTheory.EquivalenceRelation (fst p U).left (snd p q U hU).left :=
  EquivalenceRelationFiber.invariantRestrictionEquivalence e (fst_isPullback p U)
    (congrArg Over.Hom.left (inclusion_snd p q U hU))

end FLT.Mazur.InvariantOpenRelationDiagram
