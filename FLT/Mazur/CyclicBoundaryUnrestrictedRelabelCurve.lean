/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryUnrestrictedAction
public import FLT.Mazur.CyclicBoundaryLocusTestCurve

/-!
# The unrestricted relabeling retains the entire universal curve

Flattening the original base change compares the actual closed-locus curve
with its relabeled pullback. All three label factors satisfy the same comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  [SmoothOfRelativeDimension 1 E.group.hom]
local notation "B" => parameter E.group n
local notation "i" => unrestrictedMultiplicationLocusInclusion E n
local notation "g" =>
  (unrestrictedMultiplicationLocusInclusion E n ≫ Over.hom (parameter E.group n))
local notation "f" => (Over.homMk (i) rfl : Over.mk (g) ⟶ B)

/-- The universal closed-locus curve is the original curve over its actual composite base map. -/
def unrestrictedLocusFlattenIso : E.baseChange (g) ≅ unrestrictedLocusCurve E n :=
  unrestrictedTestCurveIso E n (g) (f)

/-- Flattening retains each original auxiliary and cyclic section. -/
theorem unrestrictedLocusFlattenIso_label (j : Label n) :
    markedSection E.group n (g) (f) j ≫ (unrestrictedLocusFlattenIso E n).hom.group =
      unrestrictedLocusLabel E n j :=
  unrestrictedTestCurveIso_label E n (g) (f) j

/-- The actual full curve comparison for the unrestricted common relabeling. -/
def unrestrictedRelabelCurveIso (e : RelabelGroup n) : unrestrictedLocusCurve E n ≅
    (unrestrictedLocusCurve E n).baseChange (unrestrictedRelabel E n e) :=
  (unrestrictedLocusFlattenIso E n).symm ≪≫
    unrestrictedLocusTestCurveIso E n (g) ((f) ≫ (action E.group n e).hom)
      (unrestrictedRelabel E n e) (unrestrictedRelabel_inclusion E n e)

/-- Relabeling retains every original section in all three independent factors. -/
theorem unrestrictedRelabelCurveIso_label (e : RelabelGroup n) (j : Label n) :
    unrestrictedLocusLabel E n ((labelAction n e).symm j) ≫
        (unrestrictedRelabelCurveIso E n e).hom.group =
      GroupSectionBaseChange.pullSection (unrestrictedRelabel E n e)
        (unrestrictedLocusLabel E n j) := by
  rw [← unrestrictedLocusFlattenIso_label]
  change (markedSection E.group n (g) (f) _ ≫
    (unrestrictedLocusFlattenIso E n).hom.group) ≫
      ((unrestrictedLocusFlattenIso E n).inv.group ≫ _) = _
  have he := congrArg Hom.group (unrestrictedLocusFlattenIso E n).hom_inv_id
  change (unrestrictedLocusFlattenIso E n).hom.group ≫
    (unrestrictedLocusFlattenIso E n).inv.group = 𝟙 _ at he
  rw [Category.assoc, ← Category.assoc
    (unrestrictedLocusFlattenIso E n).hom.group, he, Category.id_comp]
  rw [← section_action]
  exact unrestrictedLocusTestCurveIso_label E n (g) ((f) ≫ (action E.group n e).hom)
    (unrestrictedRelabel E n e) (unrestrictedRelabel_inclusion E n e) j

end FLT.Mazur.CyclicBoundaryParameter
