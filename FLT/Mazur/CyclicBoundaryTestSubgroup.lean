/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryUniversalSubgroup
public import FLT.Mazur.RelativeCyclicSubgroupPullbackComparison

/-!
# Original boundary test subgroups compare with the universal subgroup

Both the full curve and every original cyclic label are retained by the
comparison. This identifies reconstruction on a test with actual base change.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  [IsSeparated E.group.hom] {T : Scheme}
local notation "P" => cyclicFaithfulParameter E.group n

/-- The original ambient parameter test associated to a point of the faithful open. -/
def faithfulTestPoint (u : T ⟶ (P).left) : Over.mk (u ≫ (P).hom) ⟶ parameter E.group n := by
  exact (Over.homMk u rfl : Over.mk (u ≫ (P).hom) ⟶ (P)) ≫
    cyclicFaithfulInclusion E.group n

/-- Its original sections are universally distinct on all further tests. -/
theorem faithfulTestPoint_distinct (u : T ⟶ (P).left) :
    UniversallyDistinctSections.UniversallyDistinct (fun i : ZMod n ↦
      cyclicSectionMarking E.group n (u ≫ (P).hom) (faithfulTestPoint E n u) (.ofAdd i)) :=
  cyclicFaithfulSection_distinct E.group n (u ≫ (P).hom) (Over.homMk u rfl)

/-- The subgroup reconstructed directly from the original parameter test. -/
def faithfulTestSubgroup (u : T ⟶ (P).left) : (E.baseChange (u ≫ (P).hom)).FiniteSubgroup n :=
  (E.baseChange (u ≫ (P).hom)).relativeCyclicSubgroup
    (cyclicSectionMarking E.group n (u ≫ (P).hom) (faithfulTestPoint E n u))
    (faithfulTestPoint_distinct E n u)

/-- Each original test section is the actual monoidal pullback of its universal section. -/
theorem faithfulTestPoint_section (u : T ⟶ (P).left) (i : Multiplicative (ZMod n)) :
    cyclicSectionMarking E.group n (u ≫ (P).hom) (faithfulTestPoint E n u) i ≫
      (E.baseChangeCompIso (P).hom u).hom.group =
        GroupSectionBaseChange.pullSection u (faithfulUniversalMarking E n i) := by
  change cyclicSectionMarking E.group n (u ≫ (P).hom) (faithfulTestPoint E n u) i ≫
    (Over.pullbackComp u (P).hom).hom.app E.group = _
  apply (cancel_mono ((Over.pullbackComp u (P).hom).inv.app E.group)).mp
  rw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  change cyclicSectionMarking E.group n (u ≫ (P).hom) (faithfulTestPoint E n u) i =
    GroupSectionBaseChange.pullSection u
      (cyclicSectionMarking E.group n (P).hom (cyclicFaithfulInclusion E.group n) i) ≫ _
  rw [cyclicSectionMarking_apply, cyclicSectionMarking_apply]
  exact (section_refine E.group n (P).hom (cyclicFaithfulInclusion E.group n) u (1, 1, i)).symm

/-- The full original curve and actual test subgroup compare with the universal base change. -/
def faithfulTestSubgroupPullbackIso (u : T ⟶ (P).left) :
    FiniteSubgroup.CompatibleIso (faithfulTestSubgroup E n u)
      ((faithfulUniversalSubgroup E n).baseChange u) := by
  refine relativeCyclicSubgroupPullbackCompatibleIso
    (E := faithfulUniversalCurve E n) (F := E.baseChange (u ≫ (P).hom)) u
    (faithfulUniversalMarking E n)
    (cyclicSectionMarking E.group n (u ≫ (P).hom) (faithfulTestPoint E n u))
    (faithfulUniversalMarking_distinct E n) (faithfulTestPoint_distinct E n u)
    (E.baseChangeCompIso (P).hom u) ?_
  intro i
  exact faithfulTestPoint_section E n u i

/-- The comparison keeps the standard full-curve associativity isomorphism. -/
theorem faithfulTestSubgroupPullbackIso_curve (u : T ⟶ (P).left) :
    (faithfulTestSubgroupPullbackIso E n u).curve = E.baseChangeCompIso (P).hom u := rfl

end FLT.Mazur.CyclicBoundaryParameter
