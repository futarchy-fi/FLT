/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationFiberRebase
public import FLT.Mazur.SchemeFiniteTargetBaseChange

/-!
# Whole-fiber rebasing preserves the exact finite locus

The original scheme isomorphism over a test identifies actual finite target
neighborhoods of the two entire pullbacks. No condition on the test map or
on point-fiber cardinalities is required.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationFiber
open SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A T : Scheme} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (a : T ⟶ D)

include e in
/-- Whole original pullbacks over the two endpoints have identical finite neighborhoods. -/
theorem rebase_finiteTargetOpen :
    finiteTargetOpen (pullback.snd p (a ≫ p)) =
      finiteTargetOpen (pullback.snd p (a ≫ q)) := by
  let i := rebaseIso e a
  have H : IsPullback i.hom (pullback.snd p (a ≫ p))
      (pullback.snd p (a ≫ q)) (𝟙 T) :=
    IsPullback.of_horiz_isIso ⟨by
      simpa only [i, rebaseIso, Category.comp_id] using rebase_snd e a⟩
  have K : IsPullback i.inv (pullback.snd p (a ≫ q))
      (pullback.snd p (a ≫ p)) (𝟙 T) :=
    IsPullback.of_horiz_isIso ⟨by
      simpa only [i, rebaseIso, Category.comp_id] using unrebase_snd e a⟩
  apply le_antisymm
  · simpa using preimage_finiteTargetOpen_le K
  · simpa using preimage_finiteTargetOpen_le H

end FLT.Mazur.EquivalenceRelationFiber
