/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryUnrestrictedTestMarking
public import FLT.Mazur.CyclicMarkingSingularLocusSubgroup
public import FLT.Mazur.GeneralizedCurveGroupSectionComposition

/-!
# The full curve and all labels of a closed boundary test

The universal subgroup lives on the actual curve over the closed equation
locus. A lifted parameter test compares its pullback to the original curve,
retaining both auxiliary factors as well as the cyclic factor.
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
local notation "B" => parameter E.group n
local notation "i" => unrestrictedMultiplicationLocusInclusion E n

/-- The original generalized curve restricted to the actual closed boundary locus. -/
def unrestrictedLocusCurve : GeneralizedEllipticCurve (unrestrictedMultiplicationLocus E n) :=
  (unrestrictedUniversalCurve E n).baseChange (i)

/-- The full cyclic subgroup on the actual closed boundary locus. -/
def unrestrictedLocusSubgroup : (unrestrictedLocusCurve E n).FiniteSubgroup n :=
  (unrestrictedUniversalCurve E n).singularOrbitLocusSubgroup (unrestrictedUniversalMarking E n)

/-- Each original universal label restricts to the actual closed boundary curve. -/
def unrestrictedLocusLabel (j : Label n) :
    𝟙_ (Over (unrestrictedMultiplicationLocus E n)) ⟶ (unrestrictedLocusCurve E n).group :=
  pullSection (i) (show 𝟙_ (Over (B).left) ⟶ (unrestrictedUniversalCurve E n).group from
    markedSection E.group n (B).hom (𝟙 (B)) j)

variable (g : T ⟶ S) (f : Over.mk g ⟶ parameter E.group n)
  (k : T ⟶ unrestrictedMultiplicationLocus E n)
  (hk : k ≫ unrestrictedMultiplicationLocusInclusion E n = f.left)

/-- The lifted test compares full curves over the original source base map. -/
def unrestrictedLocusTestCurveIso : E.baseChange g ≅ (unrestrictedLocusCurve E n).baseChange k :=
  unrestrictedTestCurveIso E n g f ≪≫
    (unrestrictedUniversalCurve E n).baseChangeCompEqIso (i) k f.left hk.symm

/-- The full curve comparison retains every original auxiliary and cyclic label. -/
theorem unrestrictedLocusTestCurveIso_label (j : Label n) :
    markedSection E.group n g f j ≫ (unrestrictedLocusTestCurveIso E n g f k hk).hom.group =
      pullSection k (unrestrictedLocusLabel E n j) := by
  change markedSection E.group n g f j ≫
    ((unrestrictedTestCurveIso E n g f).hom.group ≫
      ((unrestrictedUniversalCurve E n).baseChangeCompEqIso (i) k f.left hk.symm).hom.group) = _
  rw [← Category.assoc, unrestrictedTestCurveIso_label]
  exact (unrestrictedUniversalCurve E n).baseChangeCompEqIso_groupSection (i) k f.left
    hk.symm _

end FLT.Mazur.CyclicBoundaryParameter
