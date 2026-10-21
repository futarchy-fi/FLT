/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryUnrestrictedTestMarking
public import FLT.Mazur.CyclicMarkingSingularTransport

/-!
# The closed boundary locus tests the original curve and marking

Factorization through the constructed closed locus is equivalent to the exact
orbit-subgroup condition on the original test curve, with both auxiliary
markings retained by the same parameter map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  [SmoothOfRelativeDimension 1 E.group.hom]
  (g : T ⟶ S) (f : Over.mk g ⟶ parameter E.group n)

/-- The closed boundary scheme represents the exact orbit subgroup on the original test curve. -/
theorem unrestrictedTestLocus_iff_subgroup :
    (∃ k : T ⟶ unrestrictedMultiplicationLocus E n,
      k ≫ unrestrictedMultiplicationLocusInclusion E n = f.left) ↔
      ∃ H : (E.baseChange g).FiniteSubgroup n,
        H.ideal = (E.baseChange g).cyclicMarkingIdeal (cyclicSectionMarking E.group n g f) := by
  rw [unrestrictedMultiplicationLocus_factorization_iff_subgroup]
  apply Iff.symm
  apply singularOrbitSubgroup_transport_iff
    (E := E.baseChange g) (F := (unrestrictedUniversalCurve E n).baseChange f.left)
    (cyclicSectionMarking E.group n g f)
    (pullCyclicMarking f.left (unrestrictedUniversalMarking E n))
    (unrestrictedTestCurveIso E n g f)
  intro i
  exact unrestrictedTestCurveIso_section E n g f i

/-- An original subgroup with the full cyclic orbit ideal lifts its unchanged boundary test. -/
def unrestrictedTestLocusLift (H : (E.baseChange g).FiniteSubgroup n)
    (hH : H.ideal = (E.baseChange g).cyclicMarkingIdeal (cyclicSectionMarking E.group n g f)) :
    T ⟶ unrestrictedMultiplicationLocus E n :=
  ((unrestrictedTestLocus_iff_subgroup E n g f).mpr ⟨H, hH⟩).choose

/-- The lift retains the complete original parameter, including its auxiliary markings. -/
@[reassoc] theorem unrestrictedTestLocusLift_inclusion (H : (E.baseChange g).FiniteSubgroup n)
    (hH : H.ideal = (E.baseChange g).cyclicMarkingIdeal (cyclicSectionMarking E.group n g f)) :
    unrestrictedTestLocusLift E n g f H hH ≫ unrestrictedMultiplicationLocusInclusion E n =
      f.left :=
  ((unrestrictedTestLocus_iff_subgroup E n g f).mpr ⟨H, hH⟩).choose_spec

/-- There is only one lift of the given original boundary parameter. -/
theorem unrestrictedTestLocusLift_unique (H : (E.baseChange g).FiniteSubgroup n)
    (hH : H.ideal = (E.baseChange g).cyclicMarkingIdeal (cyclicSectionMarking E.group n g f))
    (k : T ⟶ unrestrictedMultiplicationLocus E n)
    (hk : k ≫ unrestrictedMultiplicationLocusInclusion E n = f.left) :
    k = unrestrictedTestLocusLift E n g f H hH := by
  apply (cancel_mono (unrestrictedMultiplicationLocusInclusion E n)).mp
  rw [hk, unrestrictedTestLocusLift_inclusion]

end FLT.Mazur.CyclicBoundaryParameter
