/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryUnrestrictedTestLocus
public import FLT.Mazur.CyclicMarkingRelabelIdeal

/-!
# Relabeling preserves the unrestricted closed orbit condition

The full cyclic product ideal is unchanged by label permutations, including
its repeated factors. Thus the actual closed locus is invariant on every test.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  [SmoothOfRelativeDimension 1 E.group.hom]
  (g : T ⟶ S) (f : Over.mk g ⟶ parameter E.group n) (e : RelabelGroup n)

omit [SmoothOfRelativeDimension 1 E.group.hom] in
/-- The full orbit ideal is invariant under the common action on the original parameter. -/
theorem cyclicSectionMarking_action_ideal :
    (E.baseChange g).cyclicMarkingIdeal
        (cyclicSectionMarking E.group n g (f ≫ (action E.group n e).hom)) =
      (E.baseChange g).cyclicMarkingIdeal (cyclicSectionMarking E.group n g f) := by
  rw [cyclicSectionMarking_action]
  exact (E.baseChange g).cyclicMarkingIdeal_relabel _ _

/-- The actual scheme-theoretic closed-locus condition is invariant on arbitrary tests. -/
theorem unrestrictedTestLocus_action_iff :
    (∃ k : T ⟶ unrestrictedMultiplicationLocus E n,
      k ≫ unrestrictedMultiplicationLocusInclusion E n =
        (f ≫ (action E.group n e).hom).left) ↔
    (∃ k : T ⟶ unrestrictedMultiplicationLocus E n,
      k ≫ unrestrictedMultiplicationLocusInclusion E n = f.left) := by
  rw [unrestrictedTestLocus_iff_subgroup, unrestrictedTestLocus_iff_subgroup,
    cyclicSectionMarking_action_ideal]

end FLT.Mazur.CyclicBoundaryParameter
