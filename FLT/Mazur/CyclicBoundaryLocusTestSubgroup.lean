/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryLocusTestCurve
public import FLT.Mazur.CyclicMarkingSingularCompatibleTransport

/-!
# Closed boundary tests recover the actual universal subgroup

The pullback of the subgroup on the closed locus has the exact iterated
orbit ideal. Thus every original subgroup with the prescribed orbit admits
a compatible comparison to this actual universal pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  [SmoothOfRelativeDimension 1 E.group.hom]
local notation "i" => unrestrictedMultiplicationLocusInclusion E n
variable (k : T ⟶ unrestrictedMultiplicationLocus E n)

/-- The actual cyclic marking on a pullback of the closed-locus curve. -/
def unrestrictedLocusTestMarking : Multiplicative (ZMod n) →*
    (𝟙_ (Over T) ⟶ ((unrestrictedLocusCurve E n).baseChange k).group) :=
  pullCyclicMarking k (pullCyclicMarking (i) (unrestrictedUniversalMarking E n))

/-- The universal subgroup's pullback has its full orbit ideal on the whole test curve. -/
theorem unrestrictedLocusTestSubgroup_ideal :
    ((unrestrictedLocusSubgroup E n).baseChange k).ideal =
      ((unrestrictedLocusCurve E n).baseChange k).cyclicMarkingIdeal
        (unrestrictedLocusTestMarking E n k) := by
  rw [FiniteSubgroup.baseChange_ideal]
  change ((unrestrictedUniversalCurve E n).singularOrbitLocusSubgroup
    (unrestrictedUniversalMarking E n)).ideal.comap _ = _
  rw [singularOrbitLocusSubgroup_ideal]
  exact ((unrestrictedLocusCurve E n).cyclicMarkingIdeal_baseChange
    (pullCyclicMarking (i) (unrestrictedUniversalMarking E n)) k).symm

variable (g : T ⟶ S) (f : Over.mk g ⟶ parameter E.group n)
  (hk : k ≫ unrestrictedMultiplicationLocusInclusion E n = f.left)

/-- Each cyclic label agrees under the full comparison of the closed test curve. -/
theorem unrestrictedLocusTestCurveIso_cyclic (j : Multiplicative (ZMod n)) :
    cyclicSectionMarking E.group n g f j ≫
        (unrestrictedLocusTestCurveIso E n g f k hk).hom.group =
      unrestrictedLocusTestMarking E n k j := by
  rw [cyclicSectionMarking_apply]
  change _ = pullSection k (pullSection (i) (unrestrictedUniversalMarking E n j))
  have hm : unrestrictedUniversalMarking E n j =
      markedSection E.group n (parameter E.group n).hom (𝟙 _) (1, 1, j) :=
    cyclicSectionMarking_apply E.group n _ _ j
  rw [hm]
  exact unrestrictedLocusTestCurveIso_label E n g f k hk (1, 1, j)

variable (H : (E.baseChange g).FiniteSubgroup n)
  (hH : H.ideal = (E.baseChange g).cyclicMarkingIdeal (cyclicSectionMarking E.group n g f))

/-- A closed test recovers the original subgroup, with its full curve and inclusion. -/
def unrestrictedLocusTestSubgroupIso :
    FiniteSubgroup.CompatibleIso H ((unrestrictedLocusSubgroup E n).baseChange k) :=
  singularOrbitCompatibleIso (E := E.baseChange g)
    (F := (unrestrictedLocusCurve E n).baseChange k) (cyclicSectionMarking E.group n g f)
    (unrestrictedLocusTestMarking E n k) (unrestrictedLocusTestCurveIso E n g f k hk)
    (unrestrictedLocusTestCurveIso_cyclic E n k g f hk) H _ hH
    (unrestrictedLocusTestSubgroup_ideal E n k)

/-- The compatible subgroup isomorphism retains the specified full test curve comparison. -/
theorem unrestrictedLocusTestSubgroupIso_curve :
    (unrestrictedLocusTestSubgroupIso E n k g f hk H hH).curve =
      unrestrictedLocusTestCurveIso E n g f k hk :=
  singularOrbitCompatibleIso_curve _ _ _ _ _ _ _ _

/-- Every auxiliary label is retained by the actual subgroup comparison. -/
theorem unrestrictedLocusTestSubgroupIso_label (j : Label n) :
    markedSection E.group n g f j ≫
        (unrestrictedLocusTestSubgroupIso E n k g f hk H hH).curve.hom.group =
      pullSection k (unrestrictedLocusLabel E n j) := by
  rw [unrestrictedLocusTestSubgroupIso_curve]
  exact unrestrictedLocusTestCurveIso_label E n g f k hk j

end FLT.Mazur.CyclicBoundaryParameter
